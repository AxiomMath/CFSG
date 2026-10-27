module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus
public import CFSG.ClassicalInvolution.SolvableCase.SL2Three
public import CFSG.RankThree.SubgroupLists.SL2Perfect

public section

namespace CFSG.Quasithin.A38c15

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open scoped MatrixGroups

@[expose] def IsLeviBlock (p : ℕ) (K : Type) [Group K] : Prop :=
  IsSL2 p K ∨ IsExt K (fun V _ => IsElemAbelianOfRank p 2 V) (fun Y _ => IsSL2 p Y)

theorem IsLeviBlock.of_mulEquiv {p : ℕ} {K L : Type} [Group K] [Group L] (e : K ≃* L)
    (h : IsLeviBlock p K) : IsLeviBlock p L := by
  rcases h with h | h
  · exact Or.inl (IsSL2.of_mulEquiv e h)
  · exact Or.inr (A312.isExt_of_mulEquiv
      (fun _ _ _ _ e h => IsElemAbelianOfRank.of_mulEquiv e h)
      (fun _ _ _ _ e h => IsSL2.of_mulEquiv e h) e h)

@[expose] def SylowCore (p : ℕ) (Γ : Type) [Group Γ] : Prop :=
  ∀ M : Subgroup Γ, Odd M.index → M ≠ ⊤ → Group.IsSolvable ↥M ∨ IsLeviBlock p ↥(perfectCore M)

theorem isSolvable_sl2_zmod_three : Group.IsSolvable SL(2, ZMod 3) :=
  isSolvable_of_card_two_three (a := 3) (b := 1) (by
    rw [CFSG.ClassicalInvolution.natCard_sl2Three]
    norm_num)

theorem not_isPerfect_sl2_zmod_three : ¬ Group.IsPerfect SL(2, ZMod 3) := by
  intro h
  have : Nontrivial SL(2, ZMod 3) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [CFSG.ClassicalInvolution.natCard_sl2Three]
    norm_num)
  exact Group.IsPerfect.not_isSolvable SL(2, ZMod 3) isSolvable_sl2_zmod_three

theorem exists_hom_sl2_of_leviBlock {p : ℕ} [Fact p.Prime] {K : Type} [Group K]
    (h : IsLeviBlock p K) :
    ∃ f : K →* SL(2, ZMod p), Function.Surjective f ∧ (∀ a b : f.ker, a * b = b * a) ∧
      ∀ x ∈ f.ker, x ^ p = 1 := by
  rcases h with ⟨⟨e⟩⟩ | ⟨V, hV, ⟨hVe⟩, ⟨e⟩⟩
  · refine ⟨e.toMonoidHom, e.surjective, fun a b => ?_, fun x hx => ?_⟩
    · have ha : a = 1 := Subtype.ext ((e.map_eq_one_iff).mp a.2)
      have hb : b = 1 := Subtype.ext ((e.map_eq_one_iff).mp b.2)
      rw [ha, hb]
    · have : x = 1 := (e.map_eq_one_iff).mp hx
      simp [this]
  · have hker : ∀ x : K, (e.toMonoidHom.comp (QuotientGroup.mk' V)) x = 1 ↔ x ∈ V := fun x => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff x
    refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' V),
      e.surjective.comp (QuotientGroup.mk'_surjective V), fun a b => ?_, fun x hx => ?_⟩
    · have ha : a.1 ∈ V := (hker a.1).mp a.2
      have hb : b.1 ∈ V := (hker b.1).mp b.2
      apply Subtype.ext
      have := congrArg Subtype.val
        (show (⟨a.1, ha⟩ : V) * ⟨b.1, hb⟩ = ⟨b.1, hb⟩ * ⟨a.1, ha⟩ from
          hVe.injective (by
            simp only [map_mul]
            exact mul_comm _ _))
      exact this
    · have hxV : x ∈ V := (hker x).mp hx
      have h1 : (hVe ⟨x, hxV⟩) ^ p = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one]
        funext i
        simp [Pi.smul_apply]
      have h2 : (⟨x, hxV⟩ : V) ^ p = 1 := hVe.injective (by rw [map_pow, h1, map_one])
      exact congrArg Subtype.val h2

theorem ne_three_of_leviBlock {p : ℕ} [Fact p.Prime] {K : Type} [Group K] [Group.IsPerfect K]
    (h : IsLeviBlock p K) : p ≠ 3 := by
  rintro rfl
  obtain ⟨f, hf, -, -⟩ := exists_hom_sl2_of_leviBlock h
  exact not_isPerfect_sl2_zmod_three (Group.IsPerfect.ofSurjective hf)

theorem exists_hom_psl2_of_leviBlock {p : ℕ} [Fact p.Prime] {K : Type} [Group K]
    (h : IsLeviBlock p K) :
    ∃ g : K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p),
      Function.Surjective g ∧ Group.IsSolvable g.ker := by
  obtain ⟨f, hf, hcomm, -⟩ := exists_hom_sl2_of_leviBlock h
  let g : K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
    (QuotientGroup.mk' (Subgroup.center SL(2, ZMod p))).comp f
  refine ⟨g, (QuotientGroup.mk'_surjective _).comp hf, ?_⟩
  have hker : ∀ x : K, x ∈ g.ker → f x ∈ Subgroup.center SL(2, ZMod p) := fun x hx =>
    (QuotientGroup.eq_one_iff _).mp hx
  let c : g.ker →* ↥(Subgroup.center SL(2, ZMod p)) :=
    MonoidHom.codRestrict (f.comp g.ker.subtype) _ (fun a => hker a.1 a.2)
  have hcomm' : IsMulCommutative ↥(f.ker.subgroupOf g.ker) := ⟨⟨fun a b => by
    apply Subtype.ext
    apply Subtype.ext
    have := hcomm ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩
    exact congrArg (fun x : f.ker => (x : K)) this⟩⟩
  have : Group.IsSolvable ↥(f.ker.subgroupOf g.ker) := inferInstance
  have : Group.IsSolvable ↥(Subgroup.center SL(2, ZMod p)) := inferInstance
  refine Group.isSolvable_of_ker_le_range (f.ker.subgroupOf g.ker).subtype c ?_
  intro a ha
  refine ⟨⟨a, ?_⟩, rfl⟩
  have h0 : c a = 1 := ha
  have h1 := congrArg Subtype.val h0
  exact h1

theorem SylowCore.of_mulEquiv {p : ℕ} {Γ Γ' : Type} [Group Γ] [Group Γ'] [Finite Γ] [Finite Γ']
    (e : Γ ≃* Γ') (h : SylowCore p Γ') : SylowCore p Γ := by
  intro M hodd hne
  have hodd' : Odd (M.map e.toMonoidHom).index := by
    rwa [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective M]
  have hne' : M.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [map_map_symm, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
    exact this
  rcases h _ hodd' hne' with hs | hl
  · left
    exact Group.isSolvable_of_isSolvable_injective
      (f := (M.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
      (MulEquiv.injective _)
  · right
    refine IsLeviBlock.of_mulEquiv ?_ hl
    exact (MulEquiv.subgroupCongr (map_perfectCore e.toMonoidHom M)).symm.trans
      ((perfectCore M).equivMapOfInjective e.toMonoidHom e.injective).symm

theorem IsLeviBlock.eq_one_of_central {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Group K]
    (h : IsLeviBlock p K) {z : K} (hz : ∀ k : K, k * z = z * k)
    (hord : Nat.Coprime (orderOf z) (2 * p)) : z = 1 := by
  obtain ⟨f, hf, -, hker⟩ := exists_hom_sl2_of_leviBlock h
  have hcent : f z ∈ Subgroup.center SL(2, ZMod p) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := hf g
    rw [← map_mul, ← map_mul, hz k]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  have hcard := CFSG.RankThree.SubgroupLists.natCard_center_sl2 h2
  have hsq : (f z) ^ 2 = 1 := by
    have h1 := pow_card_eq_one' (G := ↥(Subgroup.center SL(2, ZMod p))) (x := ⟨f z, hcent⟩)
    rw [hcard] at h1
    exact congrArg Subtype.val h1
  have hz2 : z ^ 2 ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow, hsq]
  have hzp : (z ^ 2) ^ p = 1 := hker _ hz2
  have hord2 : Nat.Coprime (orderOf z) 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 p) hord
  have hordp : Nat.Coprime (orderOf z) p := Nat.Coprime.coprime_dvd_right (dvd_mul_left p 2) hord
  have hd1 : orderOf (z ^ 2) = 1 := by
    have hdp : orderOf (z ^ 2) ∣ p := orderOf_dvd_of_pow_eq_one hzp
    have hdz : orderOf (z ^ 2) ∣ orderOf z := orderOf_pow_dvd 2
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdz hordp) hdp
  have hz2' : z ^ 2 = 1 := orderOf_eq_one_iff.mp hd1
  have : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2'
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hord2 this)

theorem SylowCore.quotient {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Γ : Type} [Group Γ] [Finite Γ]
    (Z : Subgroup Γ) [hZn : Z.Normal] (hZc : Z ≤ Subgroup.center Γ)
    (hZ : Nat.Coprime (Nat.card Z) (2 * p)) (h : SylowCore p Γ) : SylowCore p (Γ ⧸ Z) := by
  intro M' hodd hne
  let π : Γ →* Γ ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  let M : Subgroup Γ := M'.comap π
  have hMidx : M.index = M'.index := Subgroup.index_comap_of_surjective M' hπ
  have hMmap : M.map π = M' := Subgroup.map_comap_eq_self_of_surjective hπ M'
  have hMne : M ≠ ⊤ := by
    intro htop
    apply hne
    rw [← hMmap, htop, Subgroup.map_top_of_surjective _ hπ]
  rcases h M (by rwa [hMidx]) hMne with hs | hl
  · left
    rw [← hMmap]
    exact isSolvable_map_hom π M hs
  · right
    have hinj : ∀ x ∈ perfectCore M, ∀ y ∈ perfectCore M, π x = π y → x = y := by
      intro x hx y hy hxy
      have hzm : x⁻¹ * y ∈ Z := QuotientGroup.eq.mp hxy
      let w : ↥(perfectCore M) := ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy⟩
      have hw : w = 1 := by
        refine IsLeviBlock.eq_one_of_central hp2 hl ?_ ?_
        · intro k
          apply Subtype.ext
          exact (Subgroup.mem_center_iff.mp (hZc hzm) k.1)
        · have h1 : orderOf w = orderOf (x⁻¹ * y) := (Subgroup.orderOf_coe w).symm
          rw [h1]
          exact Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard Z hzm) hZ
      have : x⁻¹ * y = 1 := congrArg Subtype.val hw
      exact inv_mul_eq_one.mp this
    exact IsLeviBlock.of_mulEquiv
      ((perfectCoreMapEquiv π M hinj).trans (MulEquiv.subgroupCongr (by rw [hMmap]))) hl

theorem odd_index_of_le_isSylowTwoOf {X : Type} [Group X] [Finite X] {T M : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hTM : T ≤ M) : Odd M.index := by
  have hidx : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right _] at this
  have : ¬ 2 ∣ M.index := fun h => hidx (h.trans (Subgroup.index_dvd_of_le hTM))
  exact Nat.odd_iff.mpr (by omega)

theorem a312For_of_sylowCore {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hX : IsPSL 3 p 1 X ∨ IsSL3 p X) (hc : SylowCore p X) :
    A312For X := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  have hTsyl := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
  generalize (P₀ : Subgroup X) = T at hTsyl
  refine A312For.of_sylow T hTsyl fun B hB hBtop => ?_
  have hB' : B ∈ cComp (B ⊔ T) := hB
  have hMne : B ⊔ T ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hodd : Odd (B ⊔ T).index := odd_index_of_le_isSylowTwoOf hTsyl le_sup_right
  rcases hc (B ⊔ T) hodd hMne with hsolv | hLevi
  · exfalso
    exact not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ T))
        (Subgroup.inclusion_injective _))
  · have hperf : Group.IsPerfect ↥(perfectCore (B ⊔ T)) :=
      Subgroup.isPerfect_iff.mpr (perfectCore_perfect (B ⊔ T))
    have hp3 : p ≠ 3 := ne_three_of_leviBlock hLevi
    have hp5 : 3 < p := by
      have := hp.two_le
      omega
    obtain ⟨f, hf, hker⟩ := exists_hom_psl2_of_leviBlock hLevi
    have hS : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2
        (ZMod p) le_rfl (Or.inr (by rw [Nat.card_zmod]; omega))
        (Or.inr (by rw [Nat.card_zmod]; omega))
    have hnab : ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p), a * b ≠ b * a :=
      CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian (ZMod p)
        (by rw [Nat.card_zmod]; omega) (by rw [Nat.card_zmod]; omega)
    have hBeq : B = perfectCore (B ⊔ T) := lFamily_eq_perfectCore hB hnab f hf hker
    have hBLevi : IsLeviBlock p ↥B :=
      IsLeviBlock.of_mulEquiv (MulEquiv.subgroupCongr hBeq.symm) hLevi
    have hLtop : IsPSL 3 p 1 ↥(⊤ : Subgroup X) ∨ IsSL3 p ↥(⊤ : Subgroup X) := by
      rcases hX with h | h
      · exact Or.inl (IsPSL.of_mulEquiv Subgroup.topEquiv.symm h)
      · exact Or.inr (IsSL3.of_mulEquiv Subgroup.topEquiv.symm h)
    rcases hBLevi with h | h
    · iterate 7 right
      left
      left
      refine ⟨true, p, hp, hp5, h, ?_⟩
      rcases hLtop with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · iterate 8 right
      left
      exact ⟨p, hp, hp5, h, hLtop⟩

end CFSG.Quasithin.A38c15
