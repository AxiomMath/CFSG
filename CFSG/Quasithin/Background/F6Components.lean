module

public import CFSG.GroupTheory.LocalCores.Components
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem isSubnormal_top_of_isSubnormal {X : Subgroup D} (hX : X.IsSubnormal) :
    IsSubnormal X ⊤ :=
  CFSG.Open.IsSubnormal.of_mathlib hX

omit [Finite D] in
theorem mem_normalizer_iff_map_conj {H : Subgroup D} {g : D} :
    g ∈ Subgroup.normalizer (H : Set D) ↔ H.map (MulAut.conj g).toMonoidHom = H := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MulEquiv.toMonoidHom_eq_coe]

omit [Finite D] in
theorem mem_normalizer_inf {A B : Subgroup D} {g : D}
    (hA : g ∈ Subgroup.normalizer (A : Set D)) (hB : g ∈ Subgroup.normalizer (B : Set D)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hA x, hB x]

theorem not_le_pCore_of_isComponent {K S : Subgroup D} (hK : CFSG.IsComponent K)
    (hS : IsSylowIn 2 S K) (hSQ : S ≤ Open.pCore 2 D) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := Open.pCore 2 D
  have hQn : Q.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hPK : Q ⊓ K ≤ K := inf_le_right
  have hSP : S ≤ Q ⊓ K := le_inf hSQ hS.1
  have hPn : ((Q ⊓ K).subgroupOf K).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    infer_instance
  have hP2 : IsPGroup 2 ↥((Q ⊓ K).subgroupOf K) :=
    ((CFSG.LieType.BorelTits.pCore_isPGroup 2).to_le inf_le_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe hPK).symm
  have hodd : Odd (Nat.card (↥K ⧸ (Q ⊓ K).subgroupOf K)) := by
    rw [← Subgroup.index_eq_card]
    have hmul := Subgroup.relIndex_mul_relIndex S (Q ⊓ K) K hSP hPK
    refine Nat.not_even_iff_odd.mp fun he => hS.2.2 ?_
    rw [← hmul]
    exact Dvd.dvd.mul_left (even_iff_two_dvd.mp he) _
  have : Group.IsSolvable (↥K ⧸ (Q ⊓ K).subgroupOf K) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsNilpotent ↥((Q ⊓ K).subgroupOf K) := hP2.isNilpotent
  have : Group.IsSolvable ↥K := Group.isSolvable_of_subgroup_quotient ((Q ⊓ K).subgroupOf K)
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect ↥K := hK.1.1
  exact Group.IsPerfect.not_isSolvable ↥K inferInstance

theorem twoResidual_le_normalizer_inf (h : IsGoldschmidtTriple G₁ G₂) {K K' : Subgroup D}
    (hK : CFSG.IsComponent K) (hK' : CFSG.IsComponent K') (hcomm : ⁅K, K'⁆ = ⊥)
    (hLK : twoResidual G₁ ≤ Subgroup.normalizer (K : Set D))
    (hLK' : twoResidual G₁ ≤ Subgroup.normalizer (K' : Set D))
    (hiff : twoResidual G₁ ≤ K ↔ twoResidual G₁ ≤ K') :
    twoResidual G₁ ≤ Subgroup.normalizer ((G₁ ⊓ G₂ ⊓ K : Subgroup D) : Set D) ⊓
      Subgroup.normalizer ((G₁ ⊓ G₂ ⊓ K' : Subgroup D) : Set D) := by
  by_cases hL : twoResidual G₁ ≤ K
  · have hL' := hiff.mp hL
    have hc : K ≤ Subgroup.centralizer (K' : Set D) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hc' : K' ≤ Subgroup.centralizer (K : Set D) := by
      rw [Subgroup.commutator_comm] at hcomm
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    refine le_inf ?_ ?_
    · refine (hL'.trans hc').trans ((Subgroup.centralizer_le ?_).trans
        (Subgroup.centralizer_le_normalizer _))
      exact inf_le_right
    · refine (hL.trans hc).trans ((Subgroup.centralizer_le ?_).trans
        (Subgroup.centralizer_le_normalizer _))
      exact inf_le_right
  · have hL' : ¬ twoResidual G₁ ≤ K' := fun h' => hL (hiff.mpr h')
    have key : ∀ {X : Subgroup D}, CFSG.IsComponent X → ¬ twoResidual G₁ ≤ X →
        twoResidual G₁ ≤ Subgroup.normalizer (X : Set D) →
        twoResidual G₁ ≤ Subgroup.normalizer ((G₁ ⊓ G₂ ⊓ X : Subgroup D) : Set D) := by
      intro X hX hLX hXN
      have hXs := isSubnormal_top_of_isSubnormal hX.2
      obtain ⟨e₁, e₂, -⟩ := ((tfae_inf_le_pCoreOf h hXs).out 3 2).mp hLX
      rw [← e₂, ← e₁]
      intro g hg
      exact mem_normalizer_inf (Subgroup.le_normalizer (twoResidual_le G₁ hg)) (hXN hg)
    exact le_inf (key hK hL hLK) (key hK' hL' hLK')

theorem f6_10 (h : IsGoldschmidtTriple G₁ G₂) {K : Subgroup D} (hK : CFSG.IsComponent K)
    (hKN : (Subgroup.normalizer (K : Set D)).index ≤ 2) :
    K.Normal ∧ ((twoResidual G₁ ≤ K ∧ K ⊔ G₂ = ⊤) ∨ (twoResidual G₂ ≤ K ∧ K ⊔ G₁ = ⊤)) ∧
      ¬ K ≤ CFSG.pPrimeCore 3 D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (K : Set D) with hNdef
  have hKs : IsSubnormal K ⊤ := isSubnormal_top_of_isSubnormal hK.2
  have hTsyl : IsSylowIn 2 (G₁ ⊓ G₂) ⊤ := isSylowTwoOf_inf_top h
  have hnot : ¬ G₁ ⊓ G₂ ⊓ K ≤ Open.pCore 2 D := fun hle =>
    not_le_pCore_of_isComponent hK (isSylowIn_inf_of_isSubnormal hKs hTsyl) hle
  have hNi : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hKn : K.Normal := by
    by_contra hKn
    have hN1 : N.index ≠ 1 := fun h1 =>
      hKn (Subgroup.normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp h1))
    have hidx : N.index = 2 := by omega
    have hNn : N.Normal := Subgroup.normal_of_index_eq_two hidx
    have hLN : twoResidual (⊤ : Subgroup D) ≤ N := by
      refine twoResidual_le_of_isTwoQuotient le_top
        (Subgroup.normalizer_eq_top_iff.mpr hNn).ge fun y _ => ⟨1, ?_⟩
      rw [pow_one, pow_two]
      exact Subgroup.mul_self_mem_of_index_two hidx y
    obtain ⟨t, htT, htN⟩ : ∃ t ∈ G₁ ⊓ G₂, t ∉ N := by
      by_contra hall
      push Not at hall
      have hmul := Subgroup.relIndex_mul_index (H := G₁ ⊓ G₂) (K := N) hall
      have h2 : 2 ∣ (G₁ ⊓ G₂).relIndex ⊤ := by
        rw [Subgroup.relIndex_top_right, ← hmul, hidx]
        exact dvd_mul_left 2 _
      exact hTsyl.2.2 h2
    set K' := K.map (MulAut.conj t).toMonoidHom with hK'def
    have hconjK : ∀ x : D, x ∈ N → K.map (MulAut.conj x).toMonoidHom = K := fun x hx =>
      mem_normalizer_iff_map_conj.mp hx
    have hconjK' : ∀ x : D, x ∉ N → K.map (MulAut.conj x).toMonoidHom = K' := by
      intro x hx
      have hs : t⁻¹ * x ∈ N := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        exact iff_of_false (fun h' => htN (by simpa using N.inv_mem h')) hx
      have e : K.map (MulAut.conj x).toMonoidHom =
          (K.map (MulAut.conj (t⁻¹ * x)).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext y
        simp [mul_assoc]
      rw [e, hconjK _ hs]
    have hmapK' : ∀ x : D,
        K'.map (MulAut.conj x).toMonoidHom = K.map (MulAut.conj (x * t)).toMonoidHom := by
      intro x
      rw [hK'def, Subgroup.map_map]
      congr 1
      ext y
      simp [mul_assoc]
    have hK'c : CFSG.IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv _ hK
    have hKK' : K ≠ K' := fun heq => htN (mem_normalizer_iff_map_conj.mpr heq.symm)
    have hcomm : ⁅K, K'⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hK hK'c).resolve_left hKK'
    have hNK' : N ≤ Subgroup.normalizer (K' : Set D) := by
      intro x hx
      rw [mem_normalizer_iff_map_conj, hmapK']
      exact hconjK' _ fun h' => htN (by simpa using N.mul_mem (N.inv_mem hx) h')
    have hiff : ∀ {G : Subgroup D}, G₁ ⊓ G₂ ≤ G → (twoResidual G ≤ K ↔ twoResidual G ≤ K') := by
      intro G hTG
      have hLt : ∀ s ∈ G₁ ⊓ G₂, (twoResidual G).map (MulAut.conj s).toMonoidHom =
          twoResidual G := fun s hs =>
        mem_normalizer_iff_map_conj.mp (le_normalizer_twoResidual G (hTG hs))
      constructor
      · intro hle
        rw [← hLt t htT]
        exact Subgroup.map_mono hle
      · intro hle
        have h1 := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hle
        rw [hLt _ ((G₁ ⊓ G₂).inv_mem htT), hK'def, Subgroup.map_map] at h1
        refine h1.trans (le_of_eq ?_)
        convert Subgroup.map_id K
        ext y
        simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
          MulAut.conj_apply, MonoidHom.id_apply]
        group
    set R := G₁ ⊓ G₂ ⊓ K ⊔ G₁ ⊓ G₂ ⊓ K' with hRdef
    have hTR : G₁ ⊓ G₂ ≤ Subgroup.normalizer (R : Set D) := by
      intro g hg
      rw [mem_normalizer_iff_map_conj, hRdef, Subgroup.map_sup,
        Subgroup.map_inf_eq (G₁ ⊓ G₂) K _ (MulAut.conj g).injective,
        Subgroup.map_inf_eq (G₁ ⊓ G₂) K' _ (MulAut.conj g).injective,
        mem_normalizer_iff_map_conj.mp (Subgroup.le_normalizer hg), hmapK']
      by_cases hgN : g ∈ N
      · have hgt : g * t ∉ N := fun h' => htN (by simpa using N.mul_mem (N.inv_mem hgN) h')
        rw [hconjK g hgN, hconjK' (g * t) hgt]
      · have hgt : g * t ∈ N := by
          rw [Subgroup.mul_mem_iff_of_index_two hidx]
          exact iff_of_false hgN htN
        rw [hconjK' g hgN, hconjK (g * t) hgt, sup_comm]
    have hLK : twoResidual (⊤ : Subgroup D) ≤ Subgroup.normalizer (K : Set D) := hLN
    have hLK' : twoResidual (⊤ : Subgroup D) ≤ Subgroup.normalizer (K' : Set D) :=
      hLN.trans hNK'
    have hL₁ := twoResidual_le_normalizer_inf h hK hK'c hcomm
      ((twoResidual_mono le_top).trans hLK) ((twoResidual_mono le_top).trans hLK')
      (hiff inf_le_left)
    have hL₂ := twoResidual_le_normalizer_inf h.symm hK hK'c hcomm
      ((twoResidual_mono le_top).trans hLK) ((twoResidual_mono le_top).trans hLK')
      (hiff inf_le_right)
    rw [inf_comm G₂ G₁] at hL₂
    have hLR : ∀ {G : Subgroup D},
        twoResidual G ≤ Subgroup.normalizer ((G₁ ⊓ G₂ ⊓ K : Subgroup D) : Set D) ⊓
          Subgroup.normalizer ((G₁ ⊓ G₂ ⊓ K' : Subgroup D) : Set D) →
        twoResidual G ≤ Subgroup.normalizer (R : Set D) :=
      fun hG _ hg => mem_normalizer_sup (hG hg).1 (hG hg).2
    have hsup : G₁ ⊔ G₂ ≤ Subgroup.normalizer (R : Set D) := by
      refine sup_le ?_ ?_
      · rw [← inf_sup_twoResidual_left h]
        exact sup_le hTR (hLR hL₁)
      · rw [← inf_sup_twoResidual_right h]
        exact sup_le hTR (hLR hL₂)
    rw [h.gen] at hsup
    have hRn : R.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hsup)
    have hRQ : R ≤ Open.pCore 2 D :=
      h.le_pCore_of_normal_le_inf (sup_le inf_le_left inf_le_left)
    exact hnot (le_sup_left.trans hRQ)
  have hLK : twoResidual G₁ ≤ K ∨ twoResidual G₂ ≤ K := by
    by_contra hn
    push Not at hn
    obtain ⟨h₁, h₂⟩ := hn
    have e₁ := ((tfae_inf_le_pCoreOf h hKs).out 3 1).mp h₁
    have e₂ := ((tfae_inf_le_pCoreOf h.symm hKs).out 3 1).mp h₂
    exact hnot (inf_le_pCore_of_normal h e₁ e₂)
  have h3 : ∀ {G G' : Subgroup D}, IsGoldschmidtTriple G G' → twoResidual G ≤ K →
      ¬ K ≤ CFSG.pPrimeCore 3 D := by
    intro G G' hG hGK hKX
    obtain ⟨x, hx, hx3⟩ := exists_orderOf_eq_three_left hG
    have hxL : x ∈ twoResidual G := mem_twoResidual_of_odd hx (by rw [hx3]; decide)
    have hdvd : orderOf x ∣ Nat.card ↥(CFSG.pPrimeCore 3 D) :=
      Subgroup.orderOf_dvd_natCard _ (hKX (hGK hxL))
    rw [hx3] at hdvd
    have hcop := CFSG.pPrimeCore_coprime_card (p := 3) (G := D)
    have := Nat.Coprime.eq_one_of_dvd hcop hdvd
    omega
  refine ⟨hKn, ?_, ?_⟩
  · rcases hLK with hL | hL
    · refine Or.inl ⟨hL, top_le_iff.mp ?_⟩
      rw [← h.gen, ← inf_sup_twoResidual_left h]
      exact sup_le (sup_le (inf_le_right.trans le_sup_right) (hL.trans le_sup_left)) le_sup_right
    · refine Or.inr ⟨hL, top_le_iff.mp ?_⟩
      rw [← h.gen, ← inf_sup_twoResidual_right h]
      exact sup_le le_sup_right (sup_le (inf_le_left.trans le_sup_right) (hL.trans le_sup_left))
  · rcases hLK with hL | hL
    · exact h3 h hL
    · exact h3 h.symm hL

end F6

end CFSG.Quasithin
