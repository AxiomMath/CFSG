module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

theorem eq_one_of_isPGroup_of_odd {G : Type*} [Group G] {P : Subgroup G} (hP : IsPGroup 2 P)
    {x : G} (hx : x ∈ P) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have h1 : orderOf x ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

theorem eq_one_of_mk_eq_one {K₀ : Type*} [Group K₀] {y : K₀}
    (hy : (y : K₀ ⧸ CFSG.pCore 2 K₀) = 1) (hodd : Odd (orderOf y)) : y = 1 :=
  eq_one_of_isPGroup_of_odd CFSG.pCore_isPGroup ((QuotientGroup.eq_one_iff y).mp hy) hodd

theorem map_eq_one_of_perfect {G H : Type*} [Group G] [Group H]
    (h : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) (f : G →* H)
    (hcomm : ∀ a b : G, f a * f b = f b * f a)
    (g : G) : f g = 1 := by
  have hle : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ f.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hcomm a b,
      mul_inv_cancel_right, mul_inv_cancel]
  exact (h ▸ hle) (Subgroup.mem_top g)

theorem perfect_quotient {G : Type*} [Group G] (h : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤)
    (M : Subgroup G) [M.Normal] :
    ⁅(⊤ : Subgroup (G ⧸ M)), (⊤ : Subgroup (G ⧸ M))⁆ = ⊤ := by
  have hs := QuotientGroup.mk'_surjective M
  rw [← Subgroup.map_top_of_surjective _ hs, ← Subgroup.map_commutator, h]

theorem mulAut_comm_of_isCyclic {P : Type*} [Group P] [IsCyclic P] (a b : MulAut P) :
    a * b = b * a := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic a.toMonoidHom
  obtain ⟨k, hk⟩ := MonoidHom.map_cyclic b.toMonoidHom
  ext g
  simp only [MulAut.mul_apply]
  change a.toMonoidHom (b.toMonoidHom g) = b.toMonoidHom (a.toMonoidHom g)
  rw [hm, hk, hk, hm, ← zpow_mul, ← zpow_mul, mul_comm]

theorem eq_bot_of_perfect_of_isPGroup {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    {p : ℕ} [Fact p.Prime] (hH : ⁅H, H⁆ = H) (hp : IsPGroup p H) : H = ⊥ := by
  by_contra hne
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  have : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
  have : Group.IsNilpotent H := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable H inferInstance

theorem card_mulAut_dvd {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {m : ℕ} (hm : Nat.card W ≤ 2 ^ m) :
    Nat.card (MulAut W) ∣ Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 W := fun w => ⟨1, by rw [pow_one]; exact hW w⟩
  obtain ⟨d, hd⟩ := hp.exists_card_eq
  have hdm : d ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).mp (hd ▸ hm)
  let ι : MulAut W →* MulAut (W × Multiplicative (Fin (m - d) → ZMod 2)) :=
    { toFun := fun a => MulEquiv.prodCongr a (MulEquiv.refl _)
      map_one' := by ext x <;> rfl
      map_mul' := fun a b => by ext x <;> rfl }
  have hι : Function.Injective ι := by
    intro a b h
    ext w
    exact congrArg (fun f : MulAut (W × Multiplicative (Fin (m - d) → ZMod 2)) => (f (w, 1)).1) h
  have hWV : Nat.card (W × Multiplicative (Fin (m - d) → ZMod 2)) = 2 ^ m := by
    have hV : Nat.card (Multiplicative (Fin (m - d) → ZMod 2)) = 2 ^ (m - d) := by
      simp [Nat.card_eq_fintype_card]
    rw [Nat.card_prod, hd, hV, ← pow_add, Nat.add_sub_cancel' hdm]
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := W × Multiplicative (Fin (m - d) → ZMod 2)) (fun a b => mul_comm a b)
    (fun a => Prod.ext (hW a.1) (by
      change (a.2 ^ 2 : Multiplicative (Fin (m - d) → ZMod 2)) = 1
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      ext i
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul])) hWV
  rw [← CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e]
  exact Subgroup.card_dvd_of_injective ι hι

theorem card_center_dvd_card_mulAut {K₀ W : Type*} [Group K₀] [Finite K₀] [Group W] [Finite W]
    (hperf : ⁅(⊤ : Subgroup K₀), (⊤ : Subgroup K₀)⁆ = ⊤)
    (hq : CFSG.IsQuasisimple (K₀ ⧸ CFSG.pCore 2 K₀))
    (ρ : K₀ →* MulAut W) (hρ : ρ ≠ 1) :
    Nat.card ((K₀ ⧸ CFSG.pCore 2 K₀) ⧸ Subgroup.center (K₀ ⧸ CFSG.pCore 2 K₀)) ∣
      Nat.card (MulAut W) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 K₀ with hO
  let φ : K₀ →* (K₀ ⧸ O) ⧸ Subgroup.center (K₀ ⧸ O) :=
    (QuotientGroup.mk' (Subgroup.center (K₀ ⧸ O))).comp (QuotientGroup.mk' O)
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hMn : (ρ.ker ⊔ O).Normal := Subgroup.sup_normal _ _
  have hNn : ((ρ.ker ⊔ O).map (QuotientGroup.mk' O)).Normal :=
    hMn.map _ (QuotientGroup.mk'_surjective O)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNn with hN | hN
  · exfalso
    have hM : ρ.ker ⊔ O = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' O) (ρ.ker ⊔ O)
      rw [hN, Subgroup.comap_top, QuotientGroup.ker_mk', sup_assoc, sup_idem] at h1
      exact h1.symm
    have hrange : ρ.range = O.map ρ := by
      rw [MonoidHom.range_eq_map, ← hM, Subgroup.map_sup,
        (Subgroup.map_eq_bot_iff ρ.ker).mpr le_rfl, bot_sup_eq]
    have hperf' : ⁅ρ.range, ρ.range⁆ = ρ.range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperf]
    have hp : IsPGroup 2 ρ.range := by
      rw [hrange]
      exact (CFSG.pCore_isPGroup (p := 2) (G := K₀)).map ρ
    exact hρ (MonoidHom.range_eq_bot_iff.mp (eq_bot_of_perfect_of_isPGroup hperf' hp))
  · have hker : ρ.ker ≤ φ.ker := fun x hx => by
      have hxN : (QuotientGroup.mk' O x) ∈ (ρ.ker ⊔ O).map (QuotientGroup.mk' O) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left hx)
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff _).mpr (hN hxN)
    have h1 : Nat.card ((K₀ ⧸ O) ⧸ Subgroup.center (K₀ ⧸ O)) = φ.ker.index := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top]
    rw [h1]
    exact (Subgroup.index_dvd_of_le hker).trans
      ((Subgroup.index_ker ρ).symm ▸ Subgroup.card_subgroup_dvd_card _)

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
