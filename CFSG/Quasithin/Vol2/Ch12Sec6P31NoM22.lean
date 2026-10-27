module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecFB
public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecNS2
public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecA8
public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecLift

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31Sec

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S126 S126P31
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

@[expose] def M22Hexad_w31 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (X S₀ : Subgroup Γ), S₀ ≤ X →
    (IsSporadic .M22 ↥X ∨ IsHat ↥X (CFSG.Blueprint.NativeSporadic.Carrier .M22)) →
    CFSG.QuasithinUnique.IsSylowTwoOf (S₀.subgroupOf X) ⊤ →
    ∃ B : Subgroup Γ, S₀ ≤ B ∧ B ≤ X ∧ AllNS (alternatingGroup (Fin 6)) ↥B ∧
      (∃ ψ : ↥(oThreePrimeResidual B) →* ↥(alternatingGroup (Fin 6)), Function.Surjective ψ) ∧
      (∀ x ∈ X, x ∈ Subgroup.normalizer (B : Set Γ) → x ∈ B) ∧
      (∀ g ∈ Subgroup.normalizer (X : Set Γ), g ∈ Subgroup.normalizer (S₀ : Set Γ) →
        g ∈ Subgroup.normalizer (B : Set Γ))

section Generic

variable {Γ : Type} [Group Γ]

theorem isSolvable_quotient_of_sup (X Z : Subgroup Γ) [X.Normal] (hXZ : X ⊔ Z = ⊤)
    (hZ : Group.IsSolvable ↥Z) : Group.IsSolvable (Γ ⧸ X) := by
  let f : ↥Z →* Γ ⧸ X := (QuotientGroup.mk' X).comp Z.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
    have hγ : γ ∈ ((X ⊔ Z : Subgroup Γ) : Set Γ) := by
      rw [hXZ]
      exact Subgroup.mem_top γ
    rw [Subgroup.normal_mul] at hγ
    obtain ⟨x, hx, z, hz, rfl⟩ := hγ
    refine ⟨⟨z, hz⟩, ?_⟩
    show (QuotientGroup.mk z : Γ ⧸ X) = QuotientGroup.mk (x * z)
    rw [QuotientGroup.eq]
    have h := (inferInstance : X.Normal).conj_mem x hx z⁻¹
    simpa [mul_assoc] using h
  exact Group.isSolvable_of_surjective hf

theorem allNS_normalizer {S : Type} [Group S] (X B : Subgroup Γ) [hX : X.Normal] (hBX : B ≤ X)
    (hself : ∀ x ∈ X, x ∈ Subgroup.normalizer (B : Set Γ) → x ∈ B) (hNS : AllNS S ↥B)
    (hsolv : Group.IsSolvable (Γ ⧸ X)) : AllNS S ↥(Subgroup.normalizer (B : Set Γ)) := by
  set Y : Subgroup Γ := Subgroup.normalizer (B : Set Γ) with hY
  have hBY : B ≤ Y := Subgroup.le_normalizer
  haveI hBn : (B.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBY).2 le_rfl
  refine AllNS.of_split (B.subgroupOf Y)
    (AllNS.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBY).symm hNS) ?_
  let ρ : ↥Y →* Γ ⧸ X := (QuotientGroup.mk' X).comp Y.subtype
  have hker : ρ.ker = B.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk (y : Γ) : Γ ⧸ X) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact ⟨fun h => hself _ h y.2, fun h => hBX h⟩
  have h1 : Group.IsSolvable (↥Y ⧸ ρ.ker) :=
    Group.isSolvable_of_isSolvable_injective (f := QuotientGroup.kerLift ρ)
      (QuotientGroup.kerLift_injective ρ)
  have h2 : Group.IsSolvable (↥Y ⧸ B.subgroupOf Y) :=
    Group.isSolvable_of_surjective (f := (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hker).surjective
  exact AllNS.of_solvable

end Generic

section Residual

variable {G : Type} [Group G]

theorem oThreePrimeResidual_le (X : Subgroup G) : oThreePrimeResidual X ≤ X :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem le_normalizer_oThreePrimeResidual (X : Subgroup G) :
    X ≤ Subgroup.normalizer (oThreePrimeResidual X : Set G) := by
  have key : ∀ g ∈ X, ∀ x ∈ oThreePrimeResidual X, g * x * g⁻¹ ∈ oThreePrimeResidual X := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyX, k, hyk⟩ := hy
      refine Subgroup.subset_closure ⟨X.mul_mem (X.mul_mem hg hyX) (X.inv_mem hg), k, ?_⟩
      have : (g * y * g⁻¹) ^ 3 ^ k = g * y ^ 3 ^ k * g⁻¹ := by
        rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← map_pow]
      rw [this, hyk]
      simp
    | one => simpa using (oThreePrimeResidual X).one_mem
    | mul a b _ _ ha hb =>
      have := (oThreePrimeResidual X).mul_mem ha hb
      simpa [mul_assoc] using this
    | inv a _ ha =>
      have := (oThreePrimeResidual X).inv_mem ha
      simpa [mul_assoc] using this
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have h := key g⁻¹ (X.inv_mem hg) _ hx
  have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [h2] at h

end Residual

section Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]
  {H K : Subgroup G}

theorem isSolvable_L1T (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) :
    Group.IsSolvable ↥(Li L F.V1 ⊔ T) := by
  have hL1 : Group.IsSolvable ↥(Li L F.V1) := P31A.isSolvable_L1 h1222 F hH
  have hTsol : Group.IsSolvable ↥T := by
    haveI := hH.hyp.sylow.1.isNilpotent
    infer_instance
  exact isSolvable_sup_of_normalizes _ _ (S126L19b.T_le_normalizer_L1 h1222 hH) hL1 hTsol

theorem two_dvd_card_of_pCoreOf_ne_bot {H : Subgroup G} (h : pCoreOf 2 H ≠ ⊥) :
    2 ∣ Nat.card ↥H := by
  have hQ1 : 1 < Nat.card ↥(pCoreOf 2 H) := (Subgroup.one_lt_card_iff_ne_bot _).2 h
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H).exists_card_eq
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  have := Subgroup.card_dvd_of_le (pCoreOf_le 2 H)
  rw [hk] at this
  exact (dvd_pow_self 2 hk1).trans this

theorem nParam_ne_zero_of_pCoreOf_ne_bot {H : Subgroup G} (h : pCoreOf 2 H ≠ ⊥) :
    E1.nParam H ≠ 0 := by
  intro h0
  obtain ⟨a, ha⟩ := E1.odd_of_nParam_le_zero (le_of_eq h0)
  have := two_dvd_card_of_pCoreOf_ne_bot h
  omega

theorem nat_card_A6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem nat_card_A8 : Nat.card ↥(alternatingGroup (Fin 8)) = 20160 := S126L1a.card_A8

end Setting

section Main

variable {G : Type} [Group G] [Finite G]

theorem noM22_w31_of (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) (hE114 : E114Used_w31)
    (hHex : M22Hexad_w31) : NoM22_w31 := by
  intro h1229 G _ _ T L V _ F hH hZ H K hIs h918 _ hK0
  have h91 := h918.toHypF98.toHypF91
  have hTH : T ≤ H := P31A.T_le_H F hIs
  have hHeq : H = conjClosure K T ⊔ (Li L F.V1 ⊔ T) := hIs.2.2
  have hK0H : conjClosure K T ≤ H := by
    rw [hHeq]
    exact le_sup_left
  have hL1TH : Li L F.V1 ⊔ T ≤ H := h918.L₁T_le_H
  have hSQTK : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hH.hyp.qtke hH.hyp.simple hH.hyp.nonabelian (pCoreOf_ne_bot h91)
  set X : Subgroup (HStar H) := star H (conjClosure K T) with hX
  haveI hXn : X.Normal := normal_star h918.K₀_normal
  have hP2 : IsPGroup 2 ↥(star H T) := P31A.isPGroup_star_T F hH hIs
  have hPmax := P31A.star_T_max F hH hIs
  have hS₀ : CFSG.QuasithinUnique.IsSylowTwoOf ((star H T ⊓ X).subgroupOf X) ⊤ :=
    P31A.isSylowTwoOf_inf_subgroupOf hP2 hPmax
  obtain ⟨B, hSB, hBX, hNS, ⟨ψ, hψ⟩, hself, hchar⟩ :=
    hHex (HStar H) X (star H T ⊓ X) inf_le_right hK0 hS₀
  have hpX : ∀ p : HStar H, p ∈ Subgroup.normalizer (X : Set (HStar H)) := fun p => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hXn]
    exact Subgroup.mem_top p
  have hPN : star H T ≤ Subgroup.normalizer (B : Set (HStar H)) := by
    intro p hp
    refine hchar p (hpX p) ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hp) x
    have h2 := Subgroup.mem_normalizer_iff.1 (hpX p) x
    rw [h1, h2]
  set Y : Subgroup (HStar H) := Subgroup.normalizer (B : Set (HStar H)) with hY
  have hBY : B ≤ Y := Subgroup.le_normalizer
  set H₀ : Subgroup G := pre H Y with hH₀
  have hH₀H : H₀ ≤ H := pre_le Y
  have hTH₀ : T ≤ H₀ := fun t ht => mem_pre.2 ⟨hTH ht, hPN (mk_mem_star (h := ⟨t, hTH ht⟩) ht)⟩
  have hO : pCoreOf 2 H ≤ pCoreOf 2 H₀ :=
    le_pCoreOf_of_le_normalizer 2 (pCoreOf_le_pre Y)
      ((pre_le Y).trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hO₂ : pCoreOf 2 H₀ ≠ ⊥ := fun h0 => pCoreOf_ne_bot h91 (le_bot_iff.1 (h0 ▸ hO))
  have hInH : InH T H₀ := ⟨hTH₀, hO₂⟩
  have hsolv : Group.IsSolvable (HStar H ⧸ X) := by
    refine isSolvable_quotient_of_sup X (star H (Li L F.V1 ⊔ T)) ?_
      (P31A.isSolvable_star (isSolvable_L1T h1222 hH))
    rw [hX, ← star_sup hK0H hL1TH, ← hHeq]
    exact star_self
  have hAllY : AllNS (alternatingGroup (Fin 6)) ↥Y := allNS_normalizer X B hBX hself hNS hsolv
  have hstar : S126.star H H₀ = Y := star_pre Y
  have hAllH₀ : AllNS (alternatingGroup (Fin 6)) ↥H₀ := by
    refine allNS_of_star hH₀H ?_
    rw [hstar]
    exact hAllY
  have hKH₀ : CFSG.SectionRank.IsKGroupCat ↥H₀ :=
    CFSG.SectionRank.IsKGroupCat.of_mulEquiv (hSQTK.2.subgroup (H₀.subgroupOf H))
      (Subgroup.subgroupOfEquivOfLe hH₀H).symm
  have hTG : IsSylowIn 2 T ⊤ :=
    ⟨le_top, hH.hyp.sylow.1, by rw [Subgroup.relIndex_top_right]; exact hH.hyp.sylow.2⟩
  have hTH₀' : IsSylowIn 2 T H₀ := by
    refine ⟨hTH₀, hTG.2.1, fun h2 => hTG.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex T H₀ ⊤ hTH₀ le_top
    rw [← this]
    exact Dvd.dvd.mul_right h2 _
  have hTsyl : IsSylowIn 2 (T.subgroupOf H₀) ⊤ := by
    rw [← E1.isSylowIn_map_of_injective H₀.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hTH₀, Subgroup.map_top, Subgroup.range_subtype]
    exact hTH₀'
  have hA6fam : lieFam1_w31 1 ↥(alternatingGroup (Fin 6)) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ⟨MulEquiv.refl _⟩⟩)))))
  have hrkA6 : ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (⊤ : Subgroup ↥(alternatingGroup (Fin 6))) ≤ 2 :=
    fun p hp hp2 => CFSG.SectionRank.pRank_alternating_le_two (by norm_num) hp hp2
  have hn1 : E1.nParam H₀ ≤ 1 := by
    have h := nParam_le_of_allNS (S := ↥(alternatingGroup (Fin 6))) (n := 1) le_rfl
      (eBound_lie hE114 le_rfl hA6fam) hKH₀ hrkA6 hAllH₀ hTsyl
    rw [E1.nParam_subgroupOf H₀]
    simpa using h
  have hnP1 : E1.nParam H₀ = 1 :=
    le_antisymm hn1 (ENat.one_le_iff_ne_zero.2 (nParam_ne_zero_of_pCoreOf_ne_bot hO₂))
  have hH₀M : H₀ ≤ Subgroup.normalizer (L : Set G) :=
    h1229 G T L V F hH hZ H₀ hInH (Or.inl hnP1)
  set J : Subgroup G := oThreePrimeResidual H₀ with hJ
  have hJL : J ≤ L := by
    have h5 := S126L1a.part5 h1222 h1228 hH
    rw [← h5]
    exact Subgroup.closure_mono fun x hx => ⟨hH₀M hx.1, hx.2⟩
  have hJH₀ : J ≤ H₀ := oThreePrimeResidual_le H₀
  have hJT : T ≤ Subgroup.normalizer (J : Set G) :=
    hTH₀.trans (le_normalizer_oThreePrimeResidual H₀)
  have hBt : oThreePrimeResidual B ≤ S126.star H J := by
    have h1 : oThreePrimeResidual (S126.star H H₀) ≤ S126.star H (oThreePrimeResidual H₀) :=
      oThreePrimeResidual_star_le hH₀H
    rw [hstar] at h1
    have hmono : oThreePrimeResidual B ≤ oThreePrimeResidual Y :=
      Subgroup.closure_mono fun x hx => ⟨hBY hx.1, hx.2⟩
    exact hmono.trans h1
  have h360 : 360 ∣ Nat.card ↥J := by
    have h1 : 360 ∣ Nat.card ↥(oThreePrimeResidual B) := by
      have := Subgroup.card_dvd_of_surjective hψ
      rwa [nat_card_A6] at this
    have h2 := h1.trans (Subgroup.card_dvd_of_le hBt)
    let f : ↥(J.subgroupOf H) →* ↥(S126.star H J) :=
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (J.subgroupOf H)
    have h3 : Nat.card ↥(S126.star H J) ∣ Nat.card ↥(J.subgroupOf H) :=
      Subgroup.card_dvd_of_surjective (f := f) (MonoidHom.subgroupMap_surjective _ _)
    have h4 : Nat.card ↥(J.subgroupOf H) = Nat.card ↥J :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hJH₀.trans hH₀H)).toEquiv
    rw [h4] at h3
    exact h2.trans h3
  have h45 : 45 ∣ Nat.card ↥((J.subgroupOf L).map (S126L19a.psi F hH)) := by
    have hc := S126L19a.card_eq F hH hJL
    obtain ⟨a, ha⟩ := S126L19a.card_inf_eq_pow h1222 hH hJL
    rw [ha] at hc
    have h45J : 45 ∣ Nat.card ↥J := (by norm_num : (45 : ℕ) ∣ 360).trans h360
    rw [hc] at h45J
    exact (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 45 2)).dvd_of_dvd_mul_right h45J
  have htop := psi_image_eq_top F hH hJL hJT h45
  let ρ : ↥J →* ↥(alternatingGroup (Fin 8)) := (S126L19a.psi F hH).comp (Subgroup.inclusion hJL)
  have hρ : Function.Surjective ρ := by
    intro a
    have ha : a ∈ (J.subgroupOf L).map (S126L19a.psi F hH) := htop ▸ Subgroup.mem_top a
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  haveI : (J.subgroupOf H₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH₀).2 (le_normalizer_oThreePrimeResidual H₀)
  have hAllJ : AllNS (alternatingGroup (Fin 6)) ↥J :=
    AllNS.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJH₀)
      (AllNS.of_normal (J.subgroupOf H₀) hAllH₀)
  have hAllA8 : AllNS (alternatingGroup (Fin 6)) ↥(alternatingGroup (Fin 8)) :=
    AllNS.of_surjective ρ hρ hAllJ
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hnab8 : ∃ a b : ↥(alternatingGroup (Fin 8)), a * b ≠ b * a := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 0 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      ⟨Equiv.swap 0 1 * Equiv.swap 0 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩, ?_⟩
    intro h
    have h2 := congrArg (fun s : ↥(alternatingGroup (Fin 8)) => (s : Equiv.Perm (Fin 8))) h
    exact absurd h2 (by decide)
  obtain ⟨e⟩ := AllNS.nonempty_equiv hAllA8 inferInstance hnab8
  have := Nat.card_congr e.toEquiv
  rw [nat_card_A8, nat_card_A6] at this
  omega

end Main

end CFSG.Quasithin.H13.P31Sec
