module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3327
public import CFSG.Quasithin.Vol2.Ch3Sec3UniqueMax
public import CFSG.GH74.KGroups.L27
public meta import CFSG.GH74.KGroups.L27
public import Certificates.Certificate5117
public import CFSG.Quasithin.Vol2.Ch3Sec3L32CenterInputs
public import Certificates.Certificate7054
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.GH74.KGroups CFSG.GH74.KGroups.L27 CFSG.Certificates

@[expose] def FactL32CenterTwo : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (A K S : Subgroup Ω), K ≤ A →
    A ≤ Subgroup.normalizer (K : Set Ω) → IsPSL 3 2 1 ↥K → (∀ a ∈ A, ∃ e : ℕ, a ^ 2 ^ e ∈ K) →
    pCoreOf 2 A = ⊥ → IsSylowTwoOf S A →
    Nat.card ↥(Subgroup.center ↥S) = 2 ∧ (Subgroup.center ↥S).map S.subtype ≤ K

namespace L32Cen

theorem chk_ok : chk₀ = true ∧ chk₁ = true ∧ chk₂ = true :=
  Certificates.certificate7054

theorem mem_cent {c π : Equiv.Perm (Fin 8)}
    (hπ : π ∈ QP.originalSubgroup) (h : c * π = π * c) :
    π ∈ cent c := by
  rw [cent, List.mem_filter]
  exact ⟨(mem_elemsT QP QP_ok π).mpr hπ, decide_eq_true h⟩

theorem center_P
    {c : Equiv.Perm (Fin 8)}
    (hc : c ∈ QP.originalSubgroup)
    (h : ∀ π ∈ QP.originalSubgroup, c * π = π * c) : c = 1 := by
  have h0 := chk_ok.1
  rw [chk₀, List.all_eq_true] at h0
  have := h0 c ((mem_elemsT QP QP_ok c).mpr hc)
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at this
  rcases this with h1 | ⟨π, hπ, hne⟩
  · exact h1
  · exact absurd (h π ((mem_elemsT QP QP_ok π).mp hπ)) hne

theorem check₁
    {σ : Equiv.Perm (Fin 8)}
    (hσ : σ ∈ QA.originalSubgroup) (h1 : σ ≠ 1)
    (h8 : 8 ≤ (cent σ).length) : σ ∈ QP.originalSubgroup := by
  have h := chk_ok.2.1
  rw [chk₁, List.all_eq_true] at h
  have := h σ ((mem_elemsT QA QA_ok σ).mpr hσ)
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this with (h' | h') | h'
  · exact absurd h' h1
  · omega
  · exact (mem_iff_sift QP QP_ok σ).mpr h'

theorem check₂
    {c h : Equiv.Perm (Fin 8)}
    (hc : c ∈ QP.originalSubgroup) (hc1 : c ≠ 1)
    (h8 : 8 ≤ (cent c).length) (hh : h ∈ QP.originalSubgroup) (hch : c * h = h * c)
    (hh1 : h ≠ 1) (hhc : h ≠ c) :
    ((cent c).filter fun π => decide (h * π = π * h)).length < 8 := by
  have h2 := chk_ok.2.2
  rw [chk₂, List.all_eq_true] at h2
  have := h2 c ((mem_elemsT QP QP_ok c).mpr hc)
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at this
  rcases this with (h' | h') | h'
  · exact absurd h' hc1
  · omega
  · have := h' h (mem_cent hh hch)
    rcases this with (h'' | h'') | h''
    · exact absurd h'' hh1
    · exact absurd h'' hhc
    · exact h''

end L32Cen

open L32Cen

variable {Ω : Type} [Group Ω] [Finite Ω]

omit [Finite Ω] in
theorem card_le_length_of_map {K X : Subgroup Ω} {P : Subgroup (Equiv.Perm (Fin 8))}
    (e : ↥K ≃* ↥P) (hXK : X ≤ K) (l : List (Equiv.Perm (Fin 8)))
    (hl : ∀ x (hx : x ∈ X), ((e ⟨x, hXK hx⟩ : ↥P) : Equiv.Perm (Fin 8)) ∈ l) :
    Nat.card ↥X ≤ l.length := by
  let f : ↥X → ↥l.toFinset := fun x =>
    ⟨(e ⟨x, hXK x.2⟩ : Equiv.Perm (Fin 8)), List.mem_toFinset.mpr (hl x x.2)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ((e ⟨x, hXK x.2⟩ : ↥P) : Equiv.Perm (Fin 8)) =
        (e ⟨y, hXK y.2⟩ : Equiv.Perm (Fin 8)) :=
      congrArg (fun t : ↥l.toFinset => (t : Equiv.Perm (Fin 8))) hxy
    have h2 := e.injective (Subtype.ext h1)
    have h3 : (x : Ω) = y := congrArg (fun t : ↥K => (t : Ω)) h2
    exact Subtype.ext h3
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_finsetCard] at this
  exact this.trans (List.toFinset_card_le l)

theorem factL32CenterTwo_holds :
    FactL32CenterTwo := by
  intro Ω _ _ A K S hKA hAK hK h2 hO hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := equiv_of_lieModel3 (K := ↥K) (Or.inl ⟨by decide, hK⟩)
  obtain ⟨M, hMP, hMA⟩ := autModel e
  have hcardK : Nat.card ↥K = 168 := by
    rw [Nat.card_congr e.toEquiv, card_group QP QP_ok, QP_valid.2]
  have hMPmem : ∀ x : ↥K, ((M.e x : M.P) : Equiv.Perm (Fin 8)) ∈ QP.originalSubgroup :=
    fun x => hMP ▸ (M.e x).2
  have hcomm : ∀ a b : ↥K, (a : Ω) * b = b * a →
      ((M.e a : M.P) : Equiv.Perm (Fin 8)) * (M.e b : Equiv.Perm (Fin 8)) =
        (M.e b : Equiv.Perm (Fin 8)) * (M.e a : Equiv.Perm (Fin 8)) := by
    intro a b hab
    have h1 : a * b = b * a := Subtype.ext hab
    have := congrArg (fun t => ((M.e t : M.P) : Equiv.Perm (Fin 8))) h1
    simpa using this
  have hZK : ∀ k ∈ K, (∀ x ∈ K, k * x = x * k) → k = 1 := by
    intro k hk hc
    have h1 : ((M.e ⟨k, hk⟩ : M.P) : Equiv.Perm (Fin 8)) = 1 := by
      refine center_P (hMPmem _) fun π hπ => ?_
      obtain ⟨y, hy⟩ := M.e.surjective ⟨π, hMP ▸ hπ⟩
      have := hcomm ⟨k, hk⟩ y (hc y y.2)
      rw [hy] at this
      exact this
    have h1' : M.e ⟨k, hk⟩ = 1 := Subtype.ext h1
    have := M.e.injective (h1'.trans (map_one M.e).symm)
    exact congrArg Subtype.val this
  have hCAK : ∀ y ∈ A, (∀ k ∈ K, y * k = k * y) → y = 1 := by
    intro y hyA hyc
    set X := A ⊓ Subgroup.centralizer (K : Set Ω) with hX
    have hXA : X ≤ A := inf_le_left
    have hAX : A ≤ Subgroup.normalizer (X : Set Ω) := fun a ha =>
      Ch3Sec3.mem_normalizer_inf (Subgroup.le_normalizer ha)
        (B2F.normalizer_le_normalizer_centralizer K (hAK ha))
    have hX2 : IsPGroup 2 ↥X := by
      intro x
      obtain ⟨n, hn⟩ := h2 x (hXA x.2)
      refine ⟨n, Subtype.ext ?_⟩
      have hxC : (x : Ω) ^ 2 ^ n ∈ Subgroup.centralizer (K : Set Ω) :=
        Subgroup.pow_mem _ (Subgroup.mem_inf.mp x.2).2 _
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hZK _ hn fun k hk => (Subgroup.mem_centralizer_iff.mp hxC k hk).symm
    have hle : X ≤ pCoreOf 2 A := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hXA hAX hX2
    rw [hO] at hle
    exact Subgroup.mem_bot.mp (hle (Subgroup.mem_inf.mpr ⟨hyA,
      Subgroup.mem_centralizer_iff.mpr fun k hk => (hyc k hk).symm⟩))
  have hS₀ : IsSylowTwoOf (S ⊓ K) K := Ch3Sec3.isSylowTwoOf_inf_of_normal hKA hAK hS
  have h8 : 8 ≤ Nat.card ↥(S ⊓ K) := by
    obtain ⟨hS₀K, -, hodd⟩ := hS₀
    have hmul := Subgroup.card_mul_index ((S ⊓ K).subgroupOf K)
    rw [hcardK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀K).toEquiv] at hmul
    have hcop : Nat.Coprime 8 ((S ⊓ K).subgroupOf K).index := by
      have : Nat.Coprime 2 ((S ⊓ K).subgroupOf K).index :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
      exact Nat.Coprime.pow_left 3 this
    have hdvd : 8 ∣ Nat.card ↥(S ⊓ K) :=
      hcop.dvd_of_dvd_mul_right ⟨21, by rw [hmul]⟩
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have key1 : ∀ z ∈ A, (∀ s ∈ S ⊓ K, z * s = s * z) → z ∈ K := by
    intro z hzA hzc
    set φ : MulAut ↥K := conjAct K ⟨z, hAK hzA⟩ with hφ
    set σ : Equiv.Perm (Fin 8) := (M.Φ φ : Equiv.Perm (Fin 8)) with hσ
    have hσA : σ ∈ QA.originalSubgroup := hMA ▸ (M.Φ φ).2
    have hφx : ∀ x : ↥K, ((φ x : ↥K) : Ω) = z * x * z⁻¹ := fun x =>
      InternalSec.coe_conjAct_apply _ x
    have hσc : ∀ s (hs : s ∈ S ⊓ K), σ * (M.e ⟨s, (Subgroup.mem_inf.mp hs).2⟩ :
        Equiv.Perm (Fin 8)) = (M.e ⟨s, (Subgroup.mem_inf.mp hs).2⟩ : Equiv.Perm (Fin 8)) * σ := by
      intro s hs
      have h1 := M.spec φ ⟨s, (Subgroup.mem_inf.mp hs).2⟩
      have hφs : φ ⟨s, (Subgroup.mem_inf.mp hs).2⟩ = ⟨s, (Subgroup.mem_inf.mp hs).2⟩ := by
        apply Subtype.ext
        rw [hφx]
        show z * s * z⁻¹ = s
        rw [hzc s hs, mul_inv_cancel_right]
      rw [hφs] at h1
      calc σ * (M.e ⟨s, _⟩ : Equiv.Perm (Fin 8)) =
          (σ * (M.e ⟨s, _⟩ : Equiv.Perm (Fin 8)) * σ⁻¹) * σ := by group
        _ = _ := by rw [← h1]
    by_cases hσ1 : σ = 1
    · have hφ1 : φ = 1 := by
        apply M.Φ.injective
        apply Subtype.ext
        rw [map_one]
        exact hσ1
      have hzc' : ∀ k ∈ K, z * k = k * z := by
        intro k hk
        have := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : ↥K) : Ω)) hφ1
        simp only [MulAut.one_apply] at this
        rw [hφx] at this
        calc z * k = (z * k * z⁻¹) * z := by group
          _ = k * z := by rw [this]
      rw [hCAK z hzA hzc']
      exact K.one_mem
    · have hcount : 8 ≤ (cent σ).length :=
        h8.trans (card_le_length_of_map M.e inf_le_right _ fun s hs =>
          mem_cent (hMPmem _) (hσc s hs))
      have hσP := check₁ hσA hσ1 hcount
      obtain ⟨w, hw⟩ := M.e.surjective ⟨σ, hMP ▸ hσP⟩
      have hφw : ∀ x : ↥K, φ x = w * x * w⁻¹ := by
        intro x
        apply M.e.injective
        apply Subtype.ext
        rw [M.spec φ x, map_mul, map_mul, map_inv, hw]
        rfl
      have hc : ∀ k ∈ K, ((w : Ω)⁻¹ * z) * k = k * ((w : Ω)⁻¹ * z) := by
        intro k hk
        have h1 := congrArg Subtype.val (hφw ⟨k, hk⟩)
        rw [hφx] at h1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
        calc (w : Ω)⁻¹ * z * k = (w : Ω)⁻¹ * (z * k * z⁻¹) * z := by group
          _ = (w : Ω)⁻¹ * ((w : Ω) * k * (w : Ω)⁻¹) * z := by rw [h1]
          _ = k * ((w : Ω)⁻¹ * z) := by group
      have h1 := hCAK _ (A.mul_mem (A.inv_mem (hKA w.2)) hzA) hc
      have hzw : z = w := by
        have := congrArg (fun t => (w : Ω) * t) h1
        simpa using this
      rw [hzw]
      exact w.2
  have hZS : (Subgroup.center ↥S).map S.subtype ≤ K := by
    rintro _ ⟨z, hz, rfl⟩
    refine key1 z (hS.1 z.2) fun s hs => ?_
    have := Subgroup.mem_center_iff.mp hz ⟨s, (Subgroup.mem_inf.mp hs).1⟩
    exact (congrArg Subtype.val this).symm
  refine ⟨?_, hZS⟩
  have huniq : ∀ z₁ z₂ : ↥(Subgroup.center ↥S), z₁ ≠ 1 → z₂ ≠ 1 → z₁ = z₂ := by
    intro z₁ z₂ h1 h2'
    by_contra hne
    have hx₁K : ((z₁ : ↥S) : Ω) ∈ K := hZS ⟨z₁, z₁.2, rfl⟩
    have hx₂K : ((z₂ : ↥S) : Ω) ∈ K := hZS ⟨z₂, z₂.2, rfl⟩
    have hcen : ∀ (z : ↥(Subgroup.center ↥S)), ∀ s ∈ S, ((z : ↥S) : Ω) * s = s * z := by
      intro z s hs
      have := Subgroup.mem_center_iff.mp z.2 ⟨s, hs⟩
      exact (congrArg Subtype.val this).symm
    have hne1 : ∀ (z : ↥(Subgroup.center ↥S)) (hz : ((z : ↥S) : Ω) ∈ K), z ≠ 1 →
        ((M.e ⟨_, hz⟩ : M.P) : Equiv.Perm (Fin 8)) ≠ 1 := by
      intro z hz hz1 h
      apply hz1
      have h' : M.e ⟨_, hz⟩ = 1 := Subtype.ext h
      have := congrArg Subtype.val (M.e.injective (h'.trans (map_one M.e).symm))
      exact Subtype.ext (Subtype.ext this)
    have hc1 := hne1 z₁ hx₁K h1
    have hh1 := hne1 z₂ hx₂K h2'
    have hhc : ((M.e ⟨_, hx₂K⟩ : M.P) : Equiv.Perm (Fin 8)) ≠ (M.e ⟨_, hx₁K⟩ : M.P) := by
      intro h
      apply hne
      have := congrArg Subtype.val (M.e.injective (Subtype.ext h))
      exact (Subtype.ext (Subtype.ext this)).symm
    have hc8 : 8 ≤ (cent (M.e ⟨_, hx₁K⟩ : Equiv.Perm (Fin 8))).length :=
      h8.trans (card_le_length_of_map M.e inf_le_right _ fun s hs =>
        mem_cent (hMPmem _) (hcomm _ _ (hcen z₁ s (Subgroup.mem_inf.mp hs).1)))
    have hlt := check₂ (hMPmem _) hc1 hc8 (hMPmem _)
      (hcomm _ _ (hcen z₁ _ (z₂ : ↥S).2)) hh1 hhc
    have hge : 8 ≤ ((cent (M.e ⟨_, hx₁K⟩ : Equiv.Perm (Fin 8))).filter fun π =>
        decide ((M.e ⟨_, hx₂K⟩ : Equiv.Perm (Fin 8)) * π = π * (M.e ⟨_, hx₂K⟩ :
          Equiv.Perm (Fin 8)))).length :=
      h8.trans (card_le_length_of_map M.e inf_le_right _ fun s hs =>
        List.mem_filter.mpr ⟨mem_cent (hMPmem _) (hcomm _ _ (hcen z₁ s (Subgroup.mem_inf.mp hs).1)),
          decide_eq_true (hcomm _ _ (hcen z₂ s (Subgroup.mem_inf.mp hs).1))⟩)
    omega
  have hS2 : IsPGroup 2 ↥S := hS.2.1
  have : Nontrivial ↥S := by
    have h1 : Nat.card ↥(S ⊓ K) ≤ Nat.card ↥S := Subgroup.card_le_of_le inf_le_left
    exact Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have := hS2.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥S))
  rw [Nat.card_eq_two_iff]
  refine ⟨1, z, hz.symm, ?_⟩
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases hy : y = 1
  · exact Or.inl hy
  · exact Or.inr (huniq y z hy hz)

theorem factL32CentralInv_of_centerTwo (h : FactL32CenterTwo) : FactL32CentralInv := by
  intro Ω _ _ A K S hKA hAK hK h2 hO hS z₁ hz₁ z₂ hz₂ hc₁ hc₂ _ _ hn₁ hn₂
  obtain ⟨hcard, -⟩ := h Ω A K S hKA hAK hK h2 hO hS
  have hmem : ∀ z (hz : z ∈ S), (∀ s ∈ S, z * s = s * z) →
      (⟨z, hz⟩ : ↥S) ∈ Subgroup.center ↥S := by
    intro z hz hc
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hc s s.2).symm
  have hne : ∀ z (hz : z ∈ S) (hc : ∀ s ∈ S, z * s = s * z), z ≠ 1 →
      (⟨⟨z, hz⟩, hmem z hz hc⟩ : ↥(Subgroup.center ↥S)) ≠ 1 := by
    intro z hz hc hz1 h
    exact hz1 (congrArg (fun t : ↥(Subgroup.center ↥S) => ((t : ↥S) : Ω)) h)
  obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp hcard
  have hall : ∀ t : ↥(Subgroup.center ↥S), t = x ∨ t = y := by
    intro t
    have : t ∈ ({x, y} : Set _) := huniv ▸ Set.mem_univ t
    simpa using this
  set t₁ : ↥(Subgroup.center ↥S) := ⟨⟨z₁, hz₁⟩, hmem z₁ hz₁ hc₁⟩
  set t₂ : ↥(Subgroup.center ↥S) := ⟨⟨z₂, hz₂⟩, hmem z₂ hz₂ hc₂⟩
  have h1 := hne z₁ hz₁ hc₁ hn₁
  have h2' := hne z₂ hz₂ hc₂ hn₂
  have heq : t₁ = t₂ := by
    rcases hall 1 with h₀ | h₀ <;> rcases hall t₁ with ha | ha <;> rcases hall t₂ with hb | hb
    all_goals first
      | exact ha.trans hb.symm
      | exact absurd (ha.trans h₀.symm) h1
      | exact absurd (hb.trans h₀.symm) h2'
  exact congrArg (fun t : ↥(Subgroup.center ↥S) => ((t : ↥S) : Ω)) heq

theorem factL32CentralInv_holds :
    FactL32CentralInv :=
  factL32CentralInv_of_centerTwo factL32CenterTwo_holds

end CFSG.Quasithin.H13
