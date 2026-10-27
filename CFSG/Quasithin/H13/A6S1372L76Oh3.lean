module

public import CFSG.Quasithin.H13.A6S1372L76Oh2
public import CFSG.Quasithin.H13.A6S1372L76Og4

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open scoped Pointwise IsMulCommutative Matrix

namespace A6L76Oh

open A6L76Of A6L76Og

theorem exists_fix_line_sp {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)}
    (hY : Group.IsPerfect ↥Y) {F : Type} [Field F] [Finite F] {n : ℕ} (hn2 : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) {π : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) →* ↥Y}
    (hπ : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSp 2 F)).RealizesVia Y (commV Y)
      (fixV Y ⊓ commV Y) π)
    {a : MulAut W} (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y)
    {P : Subgroup (MulAut W)} (hP2 : IsPGroup 2 ↥P)
    (hPodd : Odd (P.subgroupOf Y).index) {v₂ : W} (hPv : ∀ p ∈ P, p v₂ = v₂)
    (hPa : ∀ p ∈ P, p (a v₂) = a v₂ ∨ p (a v₂) = v₂ * a v₂) (hv : v₂ ∉ fixV Y) :
    ∃ g : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F), ∀ γ : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F),
      (∀ x : Fin 2 ⊕ Fin 2 → F, x (Sum.inl 1) = 0 → x (Sum.inr 0) = 0 → x (Sum.inr 1) = 0 →
        spHom (g * γ * g⁻¹) (Multiplicative.ofAdd x) = Multiplicative.ofAdd x) →
      ((π γ : ↥Y) : MulAut W) v₂ * v₂⁻¹ ∈ fixV Y ∧
        ((π γ : ↥Y) : MulAut W) (a v₂) * (a v₂)⁻¹ ∈ fixV Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨hs, -, β, hβs, hβk, hβe0⟩ := natRealizes_clean hπ
  have hβe : ∀ (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) (u : ↥(commV Y))
      (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y), β ⟨_, hu⟩ = spHom γ (β u) :=
    fun γ u hu => hβe0 γ u hu
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  have hβk' : ∀ u : ↥(commV Y), β u = 1 → (u : W) ∈ fixV Y := fun u hu => ((hβk u).1 hu).1
  have : Finite ↥Y := Finite.of_surjective π hs
  have haY' := inv_conj_mem haY
  have hconj : ∀ s γ : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F),
      ∀ x, spHom s (spHom (s⁻¹ * γ * s) x) = spHom γ (spHom s x) := by
    intro s γ x
    rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  have hcob := fun {m m' : Multiplicative (Fin 2 ⊕ Fin 2 → F)} =>
    eq_of_coboundary_eq (ρ := spHom) (fun m hm => spHom_fixed hm) (m := m) (m' := m')
  set P' : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := (P.subgroupOf Y).comap π with hP'
  have hP'2 : IsPGroup 2 ↥P' :=
    (hP2.comap_of_injective Y.subtype Y.subtype_injective).comap_of_injective π hinj
  have hP'odd : Odd P'.index := by
    rw [hP', Subgroup.index_comap_of_surjective _ hs]
    exact hPodd
  have h2 : ∀ m : Multiplicative (Fin 2 ⊕ Fin 2 → F), m * m = 1 := fun m => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    funext i
    exact CharTwo.add_self_eq_zero _
  obtain ⟨m₁, hm₁⟩ := exists_coboundary_of_odd_index h2 spHom (f := cocyc π β v₂)
    (fun g h => cocyc_mul hβe v₂ g h) hP'odd
    (fun δ hδ => cocyc_eq_one_of_fix π β (hPv _ hδ))
  have hm₁P : ∀ δ ∈ P', spHom δ m₁ = m₁ := by
    intro δ hδ
    have h := hm₁ δ
    rw [cocyc_eq_one_of_fix π β (hPv _ hδ)] at h
    exact mul_inv_eq_one.1 h.symm
  have hm₁1 : m₁ ≠ 1 := by
    intro h1
    apply hv
    refine mem_fixV_of_cocyc_eq_one hY hs hβk' fun γ => ?_
    rw [hm₁, h1, map_one, mul_inv_cancel]
  obtain ⟨f, hf⟩ := exists_lift (M := Multiplicative (Fin 2 ⊕ Fin 2 → F)) hβs hβk haY haY'
  obtain ⟨m₂, hm₂⟩ : ∃ m, m = f m₁ := ⟨_, rfl⟩
  have hcoc₂ : ∀ γ, cocyc π β (a v₂) γ = spHom γ m₂ * m₂⁻¹ := by
    rw [hm₂]
    exact cocyc_lift hβe hs hβs haY haY' hf hm₁
  obtain ⟨g, hg⟩ := exists_conj_unipotent hP'2 (fun h => by
    obtain ⟨k, hk⟩ := hP'odd
    omega)
  have hgU : ∀ u : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F), u * g = g * (g⁻¹ * u * g) :=
    fun u => by group
  obtain ⟨x₁, hx₁⟩ : ∃ x, Multiplicative.toAdd (spHom g m₁) = x := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x, Multiplicative.toAdd (spHom g m₂) = x := ⟨_, rfl⟩
  have hx₁fix : ∀ u ∈ unipotent 2 F, ((u : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ x₁ = x₁ := by
    intro u hu
    have h3 : spHom u (spHom g m₁) = spHom g m₁ := by
      rw [← MulAut.mul_apply, ← map_mul, hgU u, map_mul, MulAut.mul_apply, hm₁P _ (hg u hu)]
    have h4 := congrArg Multiplicative.toAdd h3
    rw [spHom_apply u (spHom g m₁), hx₁] at h4
    exact h4
  obtain ⟨hx₁1, hx₁2, hx₁3⟩ := unipotent_fix hx₁fix
  have hx₁0 : x₁ ≠ 0 := by
    intro h0
    apply hm₁1
    rw [← hx₁, toAdd_eq_zero, MulEquiv.map_eq_one_iff] at h0
    exact h0
  have hx₂mov : ∀ u ∈ unipotent 2 F, ((u : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ x₂ - x₂ = 0 ∨
      ((u : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ x₂ - x₂ = x₁ := by
    intro u hu
    have hsP : ((π (g⁻¹ * u * g) : ↥Y) : MulAut W) ∈ P := hg u hu
    have hcs : ∀ γ, cocyc π β (((π (g⁻¹ * u * g) : ↥Y) : MulAut W) (a v₂)) γ =
        spHom γ (spHom (g⁻¹ * u * g) m₂) * (spHom (g⁻¹ * u * g) m₂)⁻¹ := by
      intro γ
      rw [cocyc_conj hβe, hcoc₂, map_mul, map_inv, hconj]
    have hb1 : spHom u (spHom g m₂) = spHom g (spHom (g⁻¹ * u * g) m₂) := by
      rw [← MulAut.mul_apply, ← map_mul, hgU u, map_mul, MulAut.mul_apply]
    rcases hPa _ hsP with h | h
    · left
      have h3 : spHom (g⁻¹ * u * g) m₂ = m₂ := by
        refine hcob fun γ => ?_
        rw [← hcs, h, hcoc₂]
      rw [← hx₂]
      show Multiplicative.toAdd (spHom u (spHom g m₂)) - Multiplicative.toAdd (spHom g m₂) = 0
      rw [hb1, h3, sub_self]
    · right
      have h3 : spHom (g⁻¹ * u * g) m₂ = m₁ * m₂ := by
        refine hcob fun γ => ?_
        rw [← hcs, h, cocyc_mul_left, hm₁, hcoc₂, map_mul, mul_inv_rev]
        ac_rfl
      rw [← hx₂, ← hx₁]
      show Multiplicative.toAdd (spHom u (spHom g m₂)) - Multiplicative.toAdd (spHom g m₂) =
        Multiplicative.toAdd (spHom g m₁)
      rw [hb1, h3, map_mul, toAdd_mul, add_sub_cancel_right]
  have hq : 2 < Nat.card F := by
    rw [hF]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨hx₂1, hx₂2, hx₂3⟩ := unipotent_comm hq hx₁0 ⟨hx₁1, hx₁2, hx₁3⟩ hx₂mov
  refine ⟨g, fun γ hγ => ?_⟩
  have hg1 : ∀ m : Multiplicative (Fin 2 ⊕ Fin 2 → F),
      Multiplicative.toAdd (spHom g m) (Sum.inl 1) = 0 →
      Multiplicative.toAdd (spHom g m) (Sum.inr 0) = 0 →
      Multiplicative.toAdd (spHom g m) (Sum.inr 1) = 0 → spHom γ m = m := by
    intro m h1 h2 h3
    have h4 := hγ _ h1 h2 h3
    rw [ofAdd_toAdd] at h4
    have h5 : spHom (g * γ * g⁻¹) (spHom g m) = spHom g (spHom γ m) := by
      rw [← MulAut.mul_apply, ← map_mul, show g * γ * g⁻¹ * g = g * γ by group, map_mul,
        MulAut.mul_apply]
    rw [h5] at h4
    exact (spHom g).injective h4
  have hγm₁ : spHom γ m₁ = m₁ :=
    hg1 m₁ (by rw [hx₁]; exact hx₁1) (by rw [hx₁]; exact hx₁2) (by rw [hx₁]; exact hx₁3)
  have hγm₂ : spHom γ m₂ = m₂ :=
    hg1 m₂ (by rw [hx₂]; exact hx₂1) (by rw [hx₂]; exact hx₂2) (by rw [hx₂]; exact hx₂3)
  have hfix : ∀ (v : W) (m : Multiplicative (Fin 2 ⊕ Fin 2 → F)),
      (∀ δ, cocyc π β v δ = spHom δ m * m⁻¹) → spHom γ m = m →
        ((π γ : ↥Y) : MulAut W) v * v⁻¹ ∈ fixV Y := by
    intro v m hv' hm
    refine mem_fixV_of_cocyc_eq_one hY hs hβk' fun δ => ?_
    rw [cocyc_mul_left, cocyc_inv, cocyc_conj hβe, hv', hv', map_mul, map_inv, hconj, hm,
      mul_inv_cancel]
  exact ⟨hfix v₂ m₁ hm₁ hγm₁, hfix (a v₂) m₂ hcoc₂ hγm₂⟩

theorem exists_levi_sp {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)}
    (hY : Group.IsPerfect ↥Y) {F : Type} [Field F] [Finite F] {n : ℕ} (hn2 : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) {π : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) →* ↥Y}
    (hπ : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSp 2 F)).RealizesVia Y (commV Y)
      (fixV Y ⊓ commV Y) π)
    {a : MulAut W} (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y)
    {P : Subgroup (MulAut W)} (hP2 : IsPGroup 2 ↥P)
    (hPodd : Odd (P.subgroupOf Y).index) {v₂ : W} (hPv : ∀ p ∈ P, p v₂ = v₂)
    (hPa : ∀ p ∈ P, p (a v₂) = a v₂ ∨ p (a v₂) = v₂ * a v₂) (hv : v₂ ∉ fixV Y) :
    ∃ ι : Matrix.SpecialLinearGroup (Fin 2) F →* ↥Y, Function.Injective ι ∧
      ∀ A, ((ι A : ↥Y) : MulAut W) v₂ * v₂⁻¹ ∈ fixV Y ∧
        ((ι A : ↥Y) : MulAut W) (a v₂) * (a v₂)⁻¹ ∈ fixV Y := by
  obtain ⟨g, hfix⟩ := exists_fix_line_sp hY hn2 hF hπ haY hP2 hPodd hPv hPa hv
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  let cg : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) →* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
    { toFun := fun x => g⁻¹ * x * g
      map_one' := by group
      map_mul' := fun x y => by group }
  have hcg : Function.Injective cg := fun x y h => by
    have h1 : g⁻¹ * x * g = g⁻¹ * y * g := h
    simpa using h1
  refine ⟨π.comp (cg.comp leviSp1), hinj.comp (hcg.comp leviSp1_injective), fun A => ?_⟩
  refine hfix (g⁻¹ * leviSp1 A * g) fun x hx1 _ hx3 => ?_
  rw [show g * (g⁻¹ * leviSp1 A * g) * g⁻¹ = leviSp1 A by group]
  apply Multiplicative.toAdd.injective
  rw [spHom_apply, leviSp1_coe, toAdd_ofAdd]
  exact leviSpMat_mulVec hx1 hx3

end A6L76Oh

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem false_of_natSp4_ge_two (h139 : Stmt13_3_9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (h1337 : Stmt13_3_7) (hNS : ¬ LieModel G .PSp 3 2 1) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {K : Subgroup G} (hK : K ∈ cComp H) {n : ℕ} (hn2 : 2 ≤ n)
    (hSp : BinaryNaturalSp4 (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := id hSp
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨g₀, hgX, hg⟩ := S.exists_X1375_c012
  obtain ⟨a, P, v₂, rfl, -, rfl, haY, -, hP2, hPodd, hPv, hPa, -, hv⟩ :=
    S.exists_odd_config_of hH hK rfl h139 h37 h38 h13315 hgX hg
  obtain ⟨ι, hιinj, hιfix⟩ := A6L76Oh.exists_levi_sp (S.isPerfect_tilde hH hK) hn2 hF hπ haY
    hP2 hPodd hPv hPa hv
  exact S.false_of_levi h13315 h1356two h1337 hNS hH hab hK hgX hg h4 hιinj hιfix

end Setting4

theorem lem1376FiveSp4_of (h139 : Stmt13_3_9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (h1337 : Stmt13_3_7) : Lem1376FiveSp4 := by
  intro G _ _ T L V S hNS _ H hH hab _ K hK _ n hSp
  obtain ⟨F, _, _, hF, -⟩ := id hSp
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 := Finite.one_lt_card (α := F)
    rw [hF, pow_zero] at h1
    exact lt_irrefl 1 h1
  by_contra hn1
  exact S.false_of_natSp4_ge_two h139 h37 h38 h13315 h1356two h1337 hNS hH hab hK (by omega) hSp

theorem lem1376Full_of_atoms''
    (hL : Lem1376OddNCL32) (h3 : Lem1376NThree) (hG2 : Lem1376FiveG2)
    (hF : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h139 : Stmt13_3_9) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h1337 : Stmt13_3_7) : Lem1376Full :=
  lem1376Full_of_atoms' hL h3 (lem1376FiveSp4_of h139 h37 h38 h13315 h1356two h1337) hG2 hF h36
    h37 h38 h139 h13314 h13315 h1356two h1337

end CFSG.Quasithin.H13.A6
