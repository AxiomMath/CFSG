module

public import CFSG.Quasithin.H13.A6S1372L76Oi1
public import CFSG.Quasithin.H13.A6S1372L76Oh3

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open CFSG.Quasithin.Vol2.Ch11.G2Q8 (U0 InF fixed_U0 finite_cayleyGroup)
open scoped Pointwise IsMulCommutative Matrix

namespace A6L76Oi

open A6L76Of A6L76Og

theorem exists_fix_line_gen {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)}
    (hY : Group.IsPerfect ↥Y) {Γ : Type*} [Group Γ] [Finite Γ] {M : Type*} [CommGroup M]
    (hM2 : ∀ m : M, m * m = 1) {ρ : Γ →* MulAut M} (hρ : ∀ m : M, (∀ γ, ρ γ m = m) → m = 1)
    {U : Subgroup Γ}
    (hU : ∀ Q : Subgroup Γ, IsPGroup 2 ↥Q → Odd Q.index → ∃ g : Γ, ∀ x ∈ U, g⁻¹ * x * g ∈ Q)
    {L : M → Prop} (hL1 : ∀ m, (∀ u ∈ U, ρ u m = m) → L m)
    (hL2 : ∀ m₁ m₂, m₁ ≠ 1 → L m₁ → (∀ u ∈ U, ρ u m₂ = m₂ ∨ ρ u m₂ = m₁ * m₂) → L m₂)
    {π : Γ →* ↥Y} (hs : Function.Surjective π) (hinj : Function.Injective π)
    {β : ↥(commV Y) →* M} (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : W) ∈ fixV Y ⊓ commV Y)
    (hβe : ∀ (γ : Γ) (u : ↥(commV Y)) (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y),
      β ⟨_, hu⟩ = ρ γ (β u))
    {a : MulAut W} (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y)
    {P : Subgroup (MulAut W)} (hP2 : IsPGroup 2 ↥P)
    (hPodd : Odd (P.subgroupOf Y).index) {v₂ : W} (hPv : ∀ p ∈ P, p v₂ = v₂)
    (hPa : ∀ p ∈ P, p (a v₂) = a v₂ ∨ p (a v₂) = v₂ * a v₂) (hv : v₂ ∉ fixV Y) :
    ∃ g : Γ, ∀ γ : Γ, (∀ m, L m → ρ (g * γ * g⁻¹) m = m) →
      ((π γ : ↥Y) : MulAut W) v₂ * v₂⁻¹ ∈ fixV Y ∧
        ((π γ : ↥Y) : MulAut W) (a v₂) * (a v₂)⁻¹ ∈ fixV Y := by
  classical
  have hβk' : ∀ u : ↥(commV Y), β u = 1 → (u : W) ∈ fixV Y := fun u hu => ((hβk u).1 hu).1
  have : Finite ↥Y := Finite.of_surjective π hs
  have haY' := inv_conj_mem haY
  have hconj : ∀ s γ : Γ, ∀ m, ρ s (ρ (s⁻¹ * γ * s) m) = ρ γ (ρ s m) := by
    intro s γ m
    rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  have hcob := fun {m m' : M} => A6L76Oh.eq_of_coboundary_eq (ρ := ρ) hρ (m := m) (m' := m')
  set P' : Subgroup Γ := (P.subgroupOf Y).comap π with hP'
  have hP'2 : IsPGroup 2 ↥P' :=
    (hP2.comap_of_injective Y.subtype Y.subtype_injective).comap_of_injective π hinj
  have hP'odd : Odd P'.index := by
    rw [hP', Subgroup.index_comap_of_surjective _ hs]
    exact hPodd
  obtain ⟨m₁, hm₁⟩ := exists_coboundary_of_odd_index hM2 ρ (f := cocyc π β v₂)
    (fun g h => cocyc_mul hβe v₂ g h) hP'odd
    (fun δ hδ => cocyc_eq_one_of_fix π β (hPv _ hδ))
  have hm₁P : ∀ δ ∈ P', ρ δ m₁ = m₁ := by
    intro δ hδ
    have h := hm₁ δ
    rw [cocyc_eq_one_of_fix π β (hPv _ hδ)] at h
    exact mul_inv_eq_one.1 h.symm
  have hm₁1 : m₁ ≠ 1 := by
    intro h1
    apply hv
    refine mem_fixV_of_cocyc_eq_one hY hs hβk' fun γ => ?_
    rw [hm₁, h1, map_one, mul_inv_cancel]
  obtain ⟨f, hf⟩ := A6L76Oh.exists_lift (M := M) hβs hβk haY haY'
  obtain ⟨m₂, hm₂⟩ : ∃ m, m = f m₁ := ⟨_, rfl⟩
  have hcoc₂ : ∀ γ, cocyc π β (a v₂) γ = ρ γ m₂ * m₂⁻¹ := by
    rw [hm₂]
    exact A6L76Oh.cocyc_lift hβe hs hβs haY haY' hf hm₁
  obtain ⟨g, hg⟩ := hU P' hP'2 hP'odd
  have hgU : ∀ u : Γ, u * g = g * (g⁻¹ * u * g) := fun u => by group
  have hn₁L : L (ρ g m₁) := hL1 _ fun u hu => by
    rw [← MulAut.mul_apply, ← map_mul, hgU u, map_mul, MulAut.mul_apply, hm₁P _ (hg u hu)]
  have hn₁1 : ρ g m₁ ≠ 1 := fun h0 => hm₁1 ((MulEquiv.map_eq_one_iff _).1 h0)
  have hn₂mov : ∀ u ∈ U, ρ u (ρ g m₂) = ρ g m₂ ∨ ρ u (ρ g m₂) = ρ g m₁ * ρ g m₂ := by
    intro u hu
    have hsP : ((π (g⁻¹ * u * g) : ↥Y) : MulAut W) ∈ P := hg u hu
    have hcs : ∀ γ, cocyc π β (((π (g⁻¹ * u * g) : ↥Y) : MulAut W) (a v₂)) γ =
        ρ γ (ρ (g⁻¹ * u * g) m₂) * (ρ (g⁻¹ * u * g) m₂)⁻¹ := by
      intro γ
      rw [cocyc_conj hβe, hcoc₂, map_mul, map_inv, hconj]
    have hb1 : ρ u (ρ g m₂) = ρ g (ρ (g⁻¹ * u * g) m₂) := by
      rw [← MulAut.mul_apply, ← map_mul, hgU u, map_mul, MulAut.mul_apply]
    rcases hPa _ hsP with h | h
    · left
      have h3 : ρ (g⁻¹ * u * g) m₂ = m₂ := by
        refine hcob fun γ => ?_
        rw [← hcs, h, hcoc₂]
      rw [hb1, h3]
    · right
      have h3 : ρ (g⁻¹ * u * g) m₂ = m₁ * m₂ := by
        refine hcob fun γ => ?_
        rw [← hcs, h, cocyc_mul_left, hm₁, hcoc₂, map_mul, mul_inv_rev]
        ac_rfl
      rw [hb1, h3, map_mul]
  have hn₂L := hL2 _ _ hn₁1 hn₁L hn₂mov
  refine ⟨g, fun γ hγ => ?_⟩
  have hg1 : ∀ m : M, L (ρ g m) → ρ γ m = m := by
    intro m hm
    have h4 := hγ _ hm
    have h5 : ρ (g * γ * g⁻¹) (ρ g m) = ρ g (ρ γ m) := by
      rw [← MulAut.mul_apply, ← map_mul, show g * γ * g⁻¹ * g = g * γ by group, map_mul,
        MulAut.mul_apply]
    rw [h5] at h4
    exact (ρ g).injective h4
  have hfix : ∀ (v : W) (m : M), (∀ δ, cocyc π β v δ = ρ δ m * m⁻¹) → ρ γ m = m →
      ((π γ : ↥Y) : MulAut W) v * v⁻¹ ∈ fixV Y := by
    intro v m hv' hm
    refine mem_fixV_of_cocyc_eq_one hY hs hβk' fun δ => ?_
    rw [cocyc_mul_left, cocyc_inv, cocyc_conj hβe, hv', hv', map_mul, map_inv, hconj, hm,
      mul_inv_cancel]
  exact ⟨hfix v₂ m₁ hm₁ (hg1 m₁ hn₁L), hfix (a v₂) m₂ hcoc₂ (hg1 m₂ hn₂L)⟩

theorem exists_levi_g2 {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)}
    (hY : Group.IsPerfect ↥Y) {F : Type} [Field F] [Finite F] {n : ℕ} (hn2 : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) {π : ↥(quasithinG2 F) →* ↥Y}
    (hπ : (FFModel.zornQ (quasithinG2 F)).RealizesVia Y (commV Y) (fixV Y ⊓ commV Y) π)
    {a : MulAut W} (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y)
    {P : Subgroup (MulAut W)} (hP2 : IsPGroup 2 ↥P)
    (hPodd : Odd (P.subgroupOf Y).index) {v₂ : W} (hPv : ∀ p ∈ P, p v₂ = v₂)
    (hPa : ∀ p ∈ P, p (a v₂) = a v₂ ∨ p (a v₂) = v₂ * a v₂) (hv : v₂ ∉ fixV Y) :
    ∃ ι : Matrix.SpecialLinearGroup (Fin 2) F →* ↥Y, Function.Injective ι ∧
      ∀ A, ((ι A : ↥Y) : MulAut W) v₂ * v₂⁻¹ ∈ fixV Y ∧
        ((ι A : ↥Y) : MulAut W) (a v₂) * (a v₂)⁻¹ ∈ fixV Y := by
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have := finite_cayleyGroup (F := F)
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ
  obtain ⟨hs, -, β, hβs, hβk, hβe⟩ := zornRealizes_clean hπ
  let e : ↥(quasithinG2 F) ≃* ↥(cayleyGroup F) := toCay (F := F)
  let π' : ↥(cayleyGroup F) →* ↥Y := π.comp e.symm.toMonoidHom
  have hs' : Function.Surjective π' := hs.comp e.symm.surjective
  have hinj' : Function.Injective π' := hinj.comp e.symm.injective
  have hβe' : ∀ (γ : ↥(cayleyGroup F)) (u : ↥(commV Y))
      (hu : ((π' γ : ↥Y) : MulAut W) (u : W) ∈ commV Y), β ⟨_, hu⟩ = cayHom γ (β u) := by
    intro γ u hu
    refine (hβe (e.symm γ) u hu).trans ?_
    rw [MulEquiv.apply_symm_apply]
  have h2 : ∀ m : Multiplicative (Ix3 → F), m * m = 1 := fun m => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    funext i
    exact CharTwo.add_self_eq_zero _
  have hq : 2 < Nat.card F := by
    rw [hF]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨g, hfix⟩ := exists_fix_line_gen (ρ := cayHom) (U := U0 F) hY h2
    (fun m hm => cayHom_fixed hm)
    (fun Q hQ hQodd => exists_conj_U0 hF (by omega) hQ fun h => by
      obtain ⟨k, hk⟩ := hQodd
      omega)
    (L := fun m => InF 1 (Multiplicative.toAdd m))
    (fun m hm => fixed_U0 fun u hu => congrArg Multiplicative.toAdd (hm u hu))
    (fun m₁ m₂ _ hL hmov => U0_comm hq hL fun u hu => by
      rcases hmov u hu with h | h
      · left
        rw [← cayHom_apply, h, sub_self]
      · right
        rw [← cayHom_apply, h, toAdd_mul, add_sub_cancel_right])
    hs' hinj' hβs hβk hβe' haY hP2 hPodd hPv hPa hv
  let cg : ↥(cayleyGroup F) →* ↥(cayleyGroup F) :=
    { toFun := fun x => g⁻¹ * x * g
      map_one' := by group
      map_mul' := fun x y => by group }
  have hcg : Function.Injective cg := fun x y h => by
    have h1 : g⁻¹ * x * g = g⁻¹ * y * g := h
    simpa using h1
  refine ⟨π'.comp (cg.comp leviCay), hinj'.comp (hcg.comp leviCay_injective), fun A => ?_⟩
  refine hfix (g⁻¹ * leviCay A * g) fun m hm => ?_
  rw [show g * (g⁻¹ * leviCay A * g) * g⁻¹ = leviCay A by group]
  apply Multiplicative.toAdd.injective
  rw [cayHom_apply]
  exact leviCay_fix A hm

end A6L76Oi

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem false_of_natG2_ge_two (h139 : Stmt13_3_9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (h1337 : Stmt13_3_7) (hNS : ¬ LieModel G .PSp 3 2 1) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {K : Subgroup G} (hK : K ∈ cComp H) {n : ℕ} (hn2 : 2 ≤ n)
    (hG2 : G2Natural (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := id hG2
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨g₀, hgX, hg⟩ := S.exists_X1375_c012
  obtain ⟨a, P, v₂, rfl, -, rfl, haY, -, hP2, hPodd, hPv, hPa, -, hv⟩ :=
    S.exists_odd_config_of hH hK rfl h139 h37 h38 h13315 hgX hg
  obtain ⟨ι, hιinj, hιfix⟩ := A6L76Oi.exists_levi_g2 (S.isPerfect_tilde hH hK) hn2 hF hπ haY
    hP2 hPodd hPv hPa hv
  exact S.false_of_levi h13315 h1356two h1337 hNS hH hab hK hgX hg h4 hιinj hιfix

end Setting4

theorem lem1376FiveG2_of (h139 : Stmt13_3_9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (h1337 : Stmt13_3_7) : Lem1376FiveG2 := by
  intro G _ _ T L V S hNS _ H hH hab _ K hK _ n hG2
  obtain ⟨F, _, _, hF, -⟩ := id hG2
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 := Finite.one_lt_card (α := F)
    rw [hF, pow_zero] at h1
    exact lt_irrefl 1 h1
  by_contra hn1
  exact S.false_of_natG2_ge_two h139 h37 h38 h13315 h1356two h1337 hNS hH hab hK (by omega) hG2

theorem lem1376Full_of_l32_nThree
    (hL : Lem1376OddNCL32) (h3 : Lem1376NThree)
    (hF : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h139 : Stmt13_3_9) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h1337 : Stmt13_3_7) : Lem1376Full :=
  lem1376Full_of_atoms'' hL h3 (lem1376FiveG2_of h139 h37 h38 h13315 h1356two h1337) hF h36
    h37 h38 h139 h13314 h13315 h1356two h1337

end CFSG.Quasithin.H13.A6
