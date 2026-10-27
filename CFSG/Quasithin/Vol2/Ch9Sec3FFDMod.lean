module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113A7Mod
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329Alt7
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8E
public import CFSG.Quasithin.EmptyFaithful.T1515dC
public import CFSG.Quasithin.Vol2.Ch9Sec3Sp4Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct

public section

namespace CFSG.Quasithin.H13.Ch9.FFD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv Equiv.Perm
open Vol2.Ch10.SecB.C11AmS
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem commutator_le_centralizer {K J V : Subgroup G}
    (hK : K ≤ Subgroup.centralizer (V : Set G)) (hJ : J ≤ Subgroup.normalizer (V : Set G)) :
    ⁅K, J⁆ ≤ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.commutator_le]
  intro k hk j hj
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : j⁻¹ * v * j ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hJ hj)) v).mp hv
    simpa using this
  have h1 : k * v = v * k := (Subgroup.mem_centralizer_iff.mp (hK hk) v hv).symm
  have h2 : k * (j⁻¹ * v * j) = (j⁻¹ * v * j) * k :=
    (Subgroup.mem_centralizer_iff.mp (hK hk) _ hv').symm
  have e : k⁻¹ * (j⁻¹ * v * j) = (j⁻¹ * v * j) * k⁻¹ := (Commute.inv_left h2).eq
  rw [commutatorElement_def]
  calc v * (k * j * k⁻¹ * j⁻¹) = (v * k) * j * k⁻¹ * j⁻¹ := by group
    _ = (k * v) * j * k⁻¹ * j⁻¹ := by rw [← h1]
    _ = k * j * ((j⁻¹ * v * j) * k⁻¹) * j⁻¹ := by group
    _ = k * j * (k⁻¹ * (j⁻¹ * v * j)) * j⁻¹ := by rw [e]
    _ = k * j * k⁻¹ * j⁻¹ * v := by group

theorem card_modEq_card_inf_centralizer {p : ℕ} [Fact p.Prime] {P W : Subgroup G} [Finite W]
    (hP : IsPGroup p P) (hPW : P ≤ Subgroup.normalizer (W : Set G)) :
    Nat.card W ≡ Nat.card ↥(W ⊓ Subgroup.centralizer (P : Set G)) [MOD p] := by
  let _ : MulAction P W :=
    { smul := fun q w => ⟨(q : G) * w * (q : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hPW q.2) w).mp w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ((1 : P) : G) * (w : G) * ((1 : P) : G)⁻¹ = (w : G)
        simp)
      mul_smul := fun q₁ q₂ w => Subtype.ext (by
        show ((q₁ * q₂ : P) : G) * (w : G) * ((q₁ * q₂ : P) : G)⁻¹ =
          (q₁ : G) * ((q₂ : G) * (w : G) * (q₂ : G)⁻¹) * (q₁ : G)⁻¹
        simp [mul_assoc]) }
  have hsmul : ∀ (q : P) (w : W), ((q • w : W) : G) = (q : G) * w * (q : G)⁻¹ := fun _ _ => rfl
  have hmod := hP.card_modEq_card_fixedPoints W
  have hfix : Nat.card (MulAction.fixedPoints P W) =
      Nat.card ↥(W ⊓ Subgroup.centralizer (P : Set G)) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨(w : W), (w : W).2, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
        invFun := fun x => ⟨⟨x, x.2.1⟩, ?_⟩
        left_inv := fun w => rfl
        right_inv := fun x => rfl }
    · have h := congrArg Subtype.val (w.2 ⟨q, hq⟩)
      rw [hsmul] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h
    · rw [MulAction.mem_fixedPoints]
      intro q
      apply Subtype.ext
      rw [hsmul]
      have h := Subgroup.mem_centralizer_iff.mp x.2.2 q q.2
      rw [h, mul_inv_cancel_right]
  rw [hfix] at hmod
  exact hmod

theorem subsingleton_of_isPGroup_of_perfect {p : ℕ} [Fact p.Prime] {X : Type*} [Group X]
    [Finite X] (hX : IsPGroup p X) (hperf : commutator X = ⊤) : Subsingleton X := by
  by_contra hne
  rw [not_subsingleton_iff_nontrivial] at hne
  have : Group.IsNilpotent X := hX.isNilpotent
  have h := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := X)
  rw [hperf] at h
  exact lt_irrefl _ h

section AutK

variable {K V : Subgroup G}

theorem perfect_autOn (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hperf : ⁅K, K⁆ = K) :
    ⁅autOn K V, autOn K V⁆ = autOn K V := by
  have hK' : ⁅K.subgroupOf (Subgroup.normalizer (V : Set G)),
      K.subgroupOf (Subgroup.normalizer (V : Set G))⁆ =
      K.subgroupOf (Subgroup.normalizer (V : Set G)) := by
    apply Subgroup.map_injective (Subgroup.normalizer (V : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hKN, hperf]
  unfold autOn
  rw [← Subgroup.map_commutator, hK']

variable [Finite G]

theorem card_autOn_dvd (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hperf : ⁅K, K⁆ = K)
    (hA5 : Nonempty (O2Q K ≃* alternatingGroup (Fin 5)))
    (hKV : ¬ K ≤ Subgroup.centralizer (V : Set G)) : 60 ∣ Nat.card ↥(autOn K V) := by
  obtain ⟨e⟩ := hA5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := InternalSec.autOnHom hKN with hf
  have hfs : Function.Surjective f := InternalSec.autOnHom_surjective hKN
  set O := CFSG.pCore 2 ↥K with hO
  have hcard : Nat.card ↥(autOn K V) = f.ker.index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hfs, Subgroup.card_top]
  have hO60 : O.index = 60 := by
    rw [Subgroup.index, Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  set q : ↥K →* alternatingGroup (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' O) with hq
  have hqs : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective O)
  have hqker : ∀ k : ↥K, q k = 1 ↔ k ∈ O := by
    intro k
    rw [hq, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hNn : (f.ker.map q).Normal := Subgroup.Normal.map inferInstance q hqs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map q) with h | h
  · have hNO : f.ker ≤ O := by
      intro n hn
      have h1 : q n ∈ f.ker.map q := ⟨n, hn, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact (hqker n).mp h1
    rw [hcard, ← hO60]
    exact Subgroup.index_dvd_of_le hNO
  · exfalso
    apply hKV
    have hrange : ∀ k : ↥K, f k ∈ O.map f := by
      intro k
      have h1 : q k ∈ f.ker.map q := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnk⟩ := h1
      have hnO : n⁻¹ * k ∈ O := by
        rw [← hqker, map_mul, map_inv, hnk, inv_mul_cancel]
      refine ⟨n⁻¹ * k, hnO, ?_⟩
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hn, inv_one, one_mul]
    have h2 : IsPGroup 2 ↥(autOn K V) := by
      have hOf : IsPGroup 2 ↥(O.map f) := CFSG.pCore_isPGroup.map f
      intro a
      obtain ⟨k, rfl⟩ := hfs a
      obtain ⟨n, hn⟩ := hOf ⟨f k, hrange k⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    have hperfA : commutator ↥(autOn K V) = ⊤ :=
      Sp4B.commutator_eq_top_of_perfect (perfect_autOn hKN hperf)
    have hsub := subsingleton_of_isPGroup_of_perfect h2 hperfA
    intro k hk
    have h1 : f ⟨k, hk⟩ = 1 := Subsingleton.elim _ _
    exact (InternalSec.mem_ker_autOnHom hKN _).mp h1

theorem not_dvd_card_autOn (hKN : K ≤ Subgroup.normalizer (V : Set G))
    (hA5 : Nonempty (O2Q K ≃* alternatingGroup (Fin 5))) {r : ℕ} (hr : r = 7 ∨ r = 9) :
    ¬ r ∣ Nat.card ↥(autOn K V) := by
  obtain ⟨e⟩ := hA5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : Nat.card ↥(autOn K V) ∣ Nat.card ↥K := by
    have h1 := Subgroup.card_ker_mul_card_range (InternalSec.autOnHom hKN)
    rw [MonoidHom.range_eq_top.mpr (InternalSec.autOnHom_surjective hKN), Subgroup.card_top]
      at h1
    exact Dvd.intro_left _ h1
  have hK : Nat.card ↥K = 60 * Nat.card ↥(CFSG.pCore 2 ↥K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K),
      Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
  rw [hK, ha] at hdvd
  intro h
  have h1 := h.trans hdvd
  have hcop : Nat.Coprime r (2 ^ a) := by
    rcases hr with rfl | rfl <;> exact Nat.Coprime.pow_right _ (by norm_num)
  have h2 := hcop.dvd_of_dvd_mul_right h1
  rcases hr with rfl | rfl <;> exact absurd h2 (by norm_num)

end AutK

section Decomp

variable {KY V : Subgroup G} [IsMulCommutative ↥V]

theorem fixV_autOn_eq (hKYN : KY ≤ Subgroup.normalizer (V : Set G)) :
    fixV (autOn KY V) = (Subgroup.centralizer (KY : Set G)).subgroupOf V :=
  CFSG.Quasithin.AutOn.fixV_autOn_eq hKYN

theorem le_centralizer_of_le_centralizer_commutator (hKYN : KY ≤ Subgroup.normalizer (V : Set G))
    (hdir : commV (autOn KY V) ⊔ fixV (autOn KY V) = ⊤) {X : Subgroup G} (hXKY : X ≤ KY)
    (hXU : X ≤ Subgroup.centralizer ((⁅V, KY⁆ : Subgroup G) : Set G)) :
    X ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvt : (⟨v, hv⟩ : ↥V) ∈ commV (autOn KY V) ⊔ fixV (autOn KY V) := by
    rw [hdir]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hvt
  rw [commV_autOn_eq1527d hKYN, Subgroup.mem_subgroupOf] at ha
  rw [fixV_autOn_eq hKYN, Subgroup.mem_subgroupOf] at hb
  have h1 := Subgroup.mem_centralizer_iff.mp (hXU hx) _ ha
  have h2 := Subgroup.mem_centralizer_iff.mp hb x (hXKY hx)
  have hv' : (a : G) * b = v := congrArg Subtype.val hab
  rw [← hv', mul_assoc, ← h2, ← mul_assoc, h1, mul_assoc]

end Decomp

section D7

variable [Finite G] {T K KY V : Subgroup G} [IsMulCommutative ↥V]

theorem commutator_inf_centralizer_eq_bot_d7 (hKKY : K ≤ KY)
    (hKYN : KY ≤ Subgroup.normalizer (V : Set G)) (hT : IsSylowTwoOf T KY)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKperf : ⁅autOn K V, autOn K V⁆ = autOn K V) (h15 : 15 ∣ Nat.card ↥(autOn K V))
    (h7 : ¬ 7 ∣ Nat.card ↥(autOn K V)) (h9 : ¬ 9 ∣ Nat.card ↥(autOn K V))
    (hA7 : IsAlt 7 ↥(autOn KY V))
    (hnat : AlternatingNatural (autOn KY V) (commV (autOn KY V)) ⊥ 7) :
    ⁅⁅V, KY⁆, K⁆ ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := autOn KY V with hL
  set Kst := autOn K V with hKst
  set U := ⁅V, KY⁆ with hU
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKKY.trans hKYN
  have hUV : U ≤ V := A7ZK.commutator_le_left_of_le_normalizer hKYN
  have hKYU : KY ≤ Subgroup.normalizer (U : Set G) :=
    A7ZK.le_normalizer_commutator hKYN Subgroup.le_normalizer
  have hcomm : commV L = U.subgroupOf V := commV_autOn_eq1527d hKYN
  obtain ⟨π, hπ⟩ := hnat
  obtain ⟨f, -, hfk, hfe⟩ := FFC.RealizesVia.secMap Prop329.Alt7.altDn_ker_eq_bot hπ
  have : Finite (FFModel.altDn 7).Gam := (inferInstance : Finite ↥(alternatingGroup (Fin 7)))
  have hcardA : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hcardL : Nat.card ↥L = 2520 := by
    obtain ⟨e⟩ := hA7
    rw [Nat.card_congr e.toEquiv, hcardA]
  have hπinj : Function.Injective π :=
    (hπ.1.bijective_of_nat_card_le (by
      change Nat.card ↥(alternatingGroup (Fin 7)) ≤ Nat.card ↥L
      rw [hcardL, hcardA])).1
  set φ : ↥(alternatingGroup (Fin 7)) →* MulAut ↥V :=
    L.subtype.comp (π : ↥(alternatingGroup (Fin 7)) →* ↥L) with hφ
  have hφinj : Function.Injective φ := L.subtype_injective.comp hπinj
  have hφrange : φ.range = L := by
    ext a
    constructor
    · rintro ⟨γ, rfl⟩
      exact (π γ).2
    · intro ha
      obtain ⟨γ, hγ⟩ := hπ.1 ⟨a, ha⟩
      exact ⟨γ, congrArg Subtype.val hγ⟩
  have hKL : Kst ≤ L := A4.autOn_mono hKKY
  set R := Kst.comap φ with hR
  have hRmap : R.map φ = Kst := by
    rw [hR, Subgroup.map_comap_eq, hφrange, inf_of_le_right hKL]
  have hRcard : Nat.card ↥R = Nat.card ↥Kst := by
    rw [← hRmap, Subgroup.card_map_of_injective hφinj]
  have hRperf : ⁅R, R⁆ = R := by
    apply Subgroup.map_injective hφinj
    rw [Subgroup.map_commutator, hRmap, hKperf]
  set Tst := autOn T V with hTst
  have hTL : Tst ≤ L := A4.autOn_mono hT.1
  set S := Tst.comap φ with hS
  have hSmap : S.map φ = Tst := by
    rw [hS, Subgroup.map_comap_eq, hφrange, inf_of_le_right hTL]
  have hScard : Nat.card ↥S = Nat.card ↥Tst := by
    rw [← hSmap, Subgroup.card_map_of_injective hφinj]
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hKYN
  set ρ : ↥KY →* MulAut ↥V := L.subtype.comp (InternalSec.autOnHom hKYN) with hρ
  have hρrange : ρ.range = L := by
    rw [hρ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      (InternalSec.autOnHom_surjective hKYN), ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hρT : (T.subgroupOf KY).map ρ = Tst := by
    ext a
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (A4.mem_autOn_iff hTN).mpr ⟨⟨t, ht⟩, rfl⟩
    · intro ha
      obtain ⟨⟨t, ht⟩, rfl⟩ := (A4.mem_autOn_iff hTN).mp ha
      exact ⟨⟨t, hT.1 ht⟩, ht, rfl⟩
  have hTsyl := Setup.Wreath.isSylowTwoOf_map_hom hT ρ
  rw [hρT, hρrange] at hTsyl
  have hSsyl : IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hTsyl.2.1.comap_of_injective φ hφinj
    · have h1 : (S.subgroupOf ⊤).index = (Tst.subgroupOf L).index := by
        have e1 := (S.subgroupOf ⊤).card_mul_index
        have e2 := (Tst.subgroupOf L).card_mul_index
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv, hScard,
          Subgroup.card_top, hcardA] at e1
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv, hcardL] at e2
        have hpos : 0 < Nat.card ↥Tst := Nat.card_pos
        exact Nat.eq_of_mul_eq_mul_left hpos (e1.trans e2.symm)
      rw [h1]
      exact hTsyl.2.2
  have hSR : S ≤ Subgroup.normalizer (R : Set ↥(alternatingGroup (Fin 7))) := by
    intro s hs
    have hsT : φ s ∈ Tst := hs
    have hnorm := InternalSec.autOn_normal_of (U := V) hTK
    rw [Subgroup.mem_normalizer_iff]
    intro γ
    simp only [hR, Subgroup.mem_comap, map_mul, map_inv]
    refine ⟨fun hγ => hnorm _ hsT _ hγ, fun hγ => ?_⟩
    have := hnorm _ (Tst.inv_mem hsT) _ hγ
    simpa [mul_assoc] using this
  obtain ⟨g, hg⟩ := A7Std.exists_conj_eq_r0 hRperf (hRcard ▸ h15) (hRcard ▸ h7) (hRcard ▸ h9)
    hSsyl hSR
  have hRr0 : ∀ γ ∈ R, g * γ * g⁻¹ ∈ A7Std.r0 := fun γ hγ => by
    rw [← hg]
    exact ⟨γ, hγ, by simp [MulAut.conj_apply]⟩
  have hr0R : ∀ r ∈ A7Std.r0, ∃ γ ∈ R, g * γ * g⁻¹ = r := fun r hr => by
    rw [← hg] at hr
    obtain ⟨γ, hγ, rfl⟩ := hr
    exact ⟨γ, hγ, by simp [MulAut.conj_apply]⟩
  have hKR : ∀ k (hk : k ∈ K), ∃ γ ∈ R, φ γ = conjAct V ⟨k, hKN hk⟩ := fun k hk => by
    have hmem : conjAct V ⟨k, hKN hk⟩ ∈ Kst := Setup.mem_autOn_iff.2 ⟨⟨k, hKN hk⟩, hk, rfl⟩
    rw [← hRmap] at hmem
    obtain ⟨γ, hγ, hγk⟩ := hmem
    exact ⟨γ, hγ, hγk⟩
  have hRK : ∀ γ ∈ R, ∃ k : Subgroup.normalizer (V : Set G), (k : G) ∈ K ∧ conjAct V k = φ γ :=
    fun γ hγ => Setup.mem_autOn_iff.1 hγ
  have hmemC : ∀ x : ↥V, x ∈ commV L ↔ (x : G) ∈ U := fun x => by
    rw [hcomm, Subgroup.mem_subgroupOf]
  set F : ↥(commV L) →* G6.PermMod 7 :=
    (G6.permAct 7 (g : Perm (Fin 7))).toMonoidHom.comp ((G6.coreMod 7).subtype.comp f) with hF
  set fv : ↥(commV L) →* G6.PermMod 7 := (G6.coreMod 7).subtype.comp f with hfv
  have hFapp : ∀ u, F u = G6.permAct 7 (g : Perm (Fin 7)) (fv u) := fun _ => rfl
  have hfe2 : ∀ (γ : ↥(alternatingGroup (Fin 7))) (u : ↥(commV L))
      (hu : ((π γ : ↥L) : MulAut ↥V) (u : ↥V) ∈ commV L),
      fv ⟨((π γ : ↥L) : MulAut ↥V) (u : ↥V), hu⟩ = G6.permAct 7 (γ : Perm (Fin 7)) (fv u) :=
    fun γ u hu => hfe γ u hu
  have hgconj : ∀ (γ : ↥(alternatingGroup (Fin 7))) (m : G6.PermMod 7),
      G6.permAct 7 (g : Perm (Fin 7)) (G6.permAct 7 (γ : Perm (Fin 7)) m) =
        G6.permAct 7 ((g * γ * g⁻¹ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7))
          (G6.permAct 7 (g : Perm (Fin 7)) m) := fun γ m => by
    rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  set M₀ := A7ZK.e0.comap F with hM₀
  set M : Subgroup G := (M₀.map (commV L).subtype).map V.subtype with hM
  have hcommM : ⁅U, K⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro y hy k hk
    have hyV : y ∈ V := hUV hy
    have hky : k * y * k⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hKYU (hKKY hk)) y).mp hy
    obtain ⟨γ, hγR, hγk⟩ := hKR k hk
    have h1 : ((π γ : ↥L) : MulAut ↥V) = conjAct V ⟨k, hKN hk⟩ := hγk
    set u : ↥(commV L) := ⟨⟨y, hyV⟩, (hmemC _).mpr hy⟩ with hu
    have hcv : ((((π γ : ↥L) : MulAut ↥V) (u : ↥V) : ↥V) : G) = k * y * k⁻¹ := by
      rw [h1]
      rfl
    have hπu : ((π γ : ↥L) : MulAut ↥V) (u : ↥V) ∈ commV L := by
      rw [hmemC, hcv]
      exact hky
    set u' : ↥(commV L) := ⟨((π γ : ↥L) : MulAut ↥V) (u : ↥V), hπu⟩ with hu'
    have hw : ⁅y, k⁆ = (((u * u'⁻¹ : ↥(commV L)) : ↥V) : G) := by
      have hu'v : (((u' : ↥(commV L)) : ↥V) : G) = k * y * k⁻¹ := hcv
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hu'v,
        commutatorElement_def]
      show y * k * y⁻¹ * k⁻¹ = y * (k * y * k⁻¹)⁻¹
      group
    rw [hw]
    refine ⟨((u * u'⁻¹ : ↥(commV L)) : ↥V), ⟨u * u'⁻¹, ?_, rfl⟩, rfl⟩
    show F (u * u'⁻¹) ∈ A7ZK.e0
    rw [map_mul, map_inv, hFapp, hFapp, hfe2 γ u hπu, hgconj]
    exact A7ZK.mul_inv_permAct_mem_e0 _ (hRr0 γ hγR)
  rw [eq_bot_iff]
  rintro x ⟨hxUK, hxK⟩
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hcommM hxUK
  rw [Subgroup.mem_bot]
  have hwF : F w ∈ A7ZK.e0 := hw
  obtain ⟨γ, hγR, hγc⟩ := hr0R A7ZK.c5 A7ZK.c5_mem
  obtain ⟨k, hkK, hkγ⟩ := hRK γ hγR
  have hxk : (k : G) * ((w : ↥V) : G) = ((w : ↥V) : G) * (k : G) :=
    Subgroup.mem_centralizer_iff.mp hxK k hkK
  have hfix : ((π γ : ↥L) : MulAut ↥V) ((w : ↥V)) = (w : ↥V) := by
    have h1 : ((π γ : ↥L) : MulAut ↥V) = conjAct V k := hkγ.symm
    rw [h1]
    apply Subtype.ext
    show (k : G) * ((w : ↥V) : G) * (k : G)⁻¹ = ((w : ↥V) : G)
    rw [hxk, mul_inv_cancel_right]
  have hπw : ((π γ : ↥L) : MulAut ↥V) (w : ↥V) ∈ commV L := by
    rw [hfix]
    exact w.2
  have hfe' := hfe2 γ w hπw
  have hww : (⟨((π γ : ↥L) : MulAut ↥V) (w : ↥V), hπw⟩ : ↥(commV L)) = w :=
    Subtype.ext hfix
  rw [hww] at hfe'
  have hc5 : G6.permAct 7 A7ZK.c5p (F w) = F w := by
    rw [hFapp]
    have hc : (A7ZK.c5p : Perm (Fin 7)) =
        ((g * γ * g⁻¹ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) := by
      rw [hγc]
      rfl
    rw [hc, ← hgconj, ← hfe']
  have h1 := A7ZK.eq_one_of_mem_e0 hwF hc5
  rw [hFapp] at h1
  have h2 : fv w = 1 :=
    (G6.permAct 7 (g : Perm (Fin 7))).injective (h1.trans (map_one _).symm)
  have h3 : f w = 1 := Subtype.ext h2
  have h4 := (hfk w).mp h3
  rw [Subgroup.mem_bot] at h4
  show ((w : ↥V) : G) = 1
  rw [h4]
  rfl

end D7

section Four

variable [Finite G] {K KY V : Subgroup G} [IsMulCommutative ↥V]

theorem inf_centralizer_eq_bot_four (hKKY : K ≤ KY) (hKYN : KY ≤ Subgroup.normalizer (V : Set G))
    (h5 : 5 ∣ Nat.card ↥(autOn K V)) (hdir : commV (autOn KY V) ⊔ fixV (autOn KY V) = ⊤)
    (hfour : A7Four (autOn KY V) (commV (autOn KY V)) ⊥) :
    ⁅V, KY⁆ ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKKY.trans hKYN
  set U := ⁅V, KY⁆ with hU
  have hUV : U ≤ V := A7ZK.commutator_le_left_of_le_normalizer hKYN
  have hKYU : KY ≤ Subgroup.normalizer (U : Set G) :=
    A7ZK.le_normalizer_commutator hKYN Subgroup.le_normalizer
  have hcU : Nat.card ↥U = 16 := by
    have h1 := K8.card_of_a7Four_bot hfour
    rw [commV_autOn_eq1527d hKYN,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv] at h1
    exact h1
  obtain P : Sylow 5 ↥K := default
  set P' : Subgroup G := (P : Subgroup ↥K).map K.subtype with hP'
  have hP5 : IsPGroup 5 ↥P' := P.isPGroup'.map _
  have hP'K : P' ≤ K := Subgroup.map_subtype_le _
  have hPnt : ¬ P' ≤ Subgroup.centralizer (U : Set G) := by
    intro hPU
    have hPV := le_centralizer_of_le_centralizer_commutator hKYN hdir (hP'K.trans hKKY) hPU
    set f := InternalSec.autOnHom hKN with hf
    have hfs : Function.Surjective f := InternalSec.autOnHom_surjective hKN
    have hPf : (P : Subgroup ↥K).map f = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨p, hp, rfl⟩
      rw [Subgroup.mem_bot]
      exact (InternalSec.mem_ker_autOnHom hKN p).mpr (hPV ⟨p, hp, rfl⟩)
    have hidx := Subgroup.index_map_dvd (P : Subgroup ↥K) hfs
    rw [hPf, Subgroup.index_bot] at hidx
    exact P.not_dvd_index (h5.trans hidx)
  have hPU : P' ≤ Subgroup.normalizer (U : Set G) := (hP'K.trans hKKY).trans hKYU
  have : Finite ↥U := Nat.finite_of_card_ne_zero (by rw [hcU]; norm_num)
  have hmod := card_modEq_card_inf_centralizer hP5 hPU
  rw [hcU] at hmod
  have hdvd : Nat.card ↥(U ⊓ Subgroup.centralizer (P' : Set G)) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 from rfl, ← hcU]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨c, hc4, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hc4' : c ≠ 4 := by
    rintro rfl
    apply hPnt
    have heq : U ⊓ Subgroup.centralizer (P' : Set G) = U :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, hcU]; norm_num)
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ U ⊓ Subgroup.centralizer (P' : Set G) := by rw [heq]; exact hu
    exact (Subgroup.mem_centralizer_iff.mp hu'.2 p hp).symm
  have hc0 : c = 0 := by
    rw [hc] at hmod
    have key : ∀ c < 5, c ≠ 4 → 16 ≡ 2 ^ c [MOD 5] → c = 0 := by decide
    exact key c (by omega) hc4' hmod
  rw [hc0, pow_zero, Subgroup.card_eq_one] at hc
  rw [eq_bot_iff]
  rintro x ⟨hxU, hxK⟩
  have hx : x ∈ U ⊓ Subgroup.centralizer (P' : Set G) :=
    ⟨hxU, Subgroup.centralizer_le hP'K hxK⟩
  rw [hc] at hx
  exact hx

end Four

end CFSG.Quasithin.H13.Ch9.FFD
