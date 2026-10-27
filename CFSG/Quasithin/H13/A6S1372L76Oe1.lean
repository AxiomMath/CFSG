module

public import CFSG.Quasithin.H13.A6S1372L76Od2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76Oe

open A6L76Od

theorem permAct_w5 (σ : Perm (Fin 5)) (j : Fin 5) :
    G6.permAct 5 σ (Multiplicative.ofAdd (w5 j)) = Multiplicative.ofAdd (w5 (σ j)) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply, toAdd_ofAdd, toAdd_ofAdd]
  simp only [w5]
  by_cases h : i = σ j
  · subst h
    simp
  · have h' : σ.symm i ≠ j := fun h' => h (by rw [← h']; simp)
    simp [h, h']

theorem kleinV0_fixed : ∀ v : Fin 5 → ZMod 2, ∑ i, v i = 0 →
    (∀ b ∈ A7.kleinV0Set, ∀ i, v (b⁻¹ i) = v i) → v = 0 ∨ v = w5 4 := by
  decide +kernel

theorem kleinV0_moved : ∀ j : Fin 5, (∀ b ∈ A7.kleinV0Set,
    (fun i => w5 j (b⁻¹ i)) = w5 j ∨ (fun i => w5 j (b⁻¹ i)) = w5 4 + w5 j) → j = 4 := by
  decide +kernel

theorem alt5_fixed : ∀ v : Fin 5 → ZMod 2, ∑ i, v i = 0 →
    (∀ i, v ((cyc 0 1 2)⁻¹ i) = v i) → (∀ i, v ((cyc 2 3 4)⁻¹ i) = v i) → v = 0 := by
  decide +kernel

theorem cyc_sign : Perm.sign (cyc 0 1 2) = 1 ∧ Perm.sign (cyc 2 3 4) = 1 := by
  decide +kernel

theorem coreMod_sq (m : ↥(G6.coreMod 5)) : m * m = 1 := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  show Multiplicative.toAdd ((m : G6.PermMod 5)) i + Multiplicative.toAdd ((m : G6.PermMod 5)) i = 0
  exact CharTwo.add_self_eq_zero _

theorem eq_one_of_fixed (m : ↥(G6.coreMod 5))
    (hm : ∀ γ : ↥(alternatingGroup (Fin 5)), G6.coreAct 5 (γ : Perm (Fin 5)) m = m) : m = 1 := by
  have h1 := hm ⟨cyc 0 1 2, Perm.mem_alternatingGroup.2 cyc_sign.1⟩
  have h2 := hm ⟨cyc 2 3 4, Perm.mem_alternatingGroup.2 cyc_sign.2⟩
  have e1 : ∀ i, Multiplicative.toAdd ((m : G6.PermMod 5)) ((cyc 0 1 2)⁻¹ i) =
      Multiplicative.toAdd ((m : G6.PermMod 5)) i := fun i =>
    congrFun (congrArg Multiplicative.toAdd (congrArg Subtype.val h1)) i
  have e2 : ∀ i, Multiplicative.toAdd ((m : G6.PermMod 5)) ((cyc 2 3 4)⁻¹ i) =
      Multiplicative.toAdd ((m : G6.PermMod 5)) i := fun i =>
    congrFun (congrArg Multiplicative.toAdd (congrArg Subtype.val h2)) i
  have h := alt5_fixed _ m.2 e1 e2
  exact Subtype.ext (Multiplicative.toAdd.injective h)

variable {W : Type*} [CommGroup W]

theorem altRealizes_clean {Y : Subgroup (MulAut W)} {U Z : Subgroup W}
    {π : ↥(alternatingGroup (Fin 5)) →* ↥Y} (h : (FFModel.altDn 5).RealizesVia Y U Z π) :
    Function.Surjective π ∧ (∀ y : ↥Y, ∀ u ∈ U, (y : MulAut W) u ∈ U) ∧
      ∃ β : ↥U →* ↥(G6.coreMod 5), Function.Surjective β ∧ (∀ u, β u = 1 ↔ (u : W) ∈ Z) ∧
        ∀ (γ : ↥(alternatingGroup (Fin 5))) (u : ↥U)
          (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ U),
          β ⟨_, hu⟩ = G6.coreAct 5 (γ : Perm (Fin 5)) (β u) := by
  obtain ⟨hs, -, -, hU, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  let e : (↥(FFModel.altDn 5).sec ⧸ (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) ≃*
      ↥(G6.coreMod 5) :=
    (QuotientGroup.quotientMulEquivOfEq (show (FFModel.altDn 5).ker.subgroupOf
      (FFModel.altDn 5).sec = ⊥ by rw [A7.altDn_five_ker_eq_bot, Subgroup.bot_subgroupOf])).trans
      QuotientGroup.quotientBot
  refine ⟨hs, hU, e.toMonoidHom.comp β, e.surjective.comp hβs, fun u => ?_, fun γ u hu => ?_⟩
  · show e (β u) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact hβk u
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have h1 := hβe γ u m hu (hsec γ _ m.2) hm.symm
    show e (β ⟨_, hu⟩) = G6.coreAct 5 _ (e (β u))
    refine (congrArg e h1).trans ?_
    rw [← hm]
    rfl

theorem gen_mem_commV {Y : Subgroup (MulAut W)} {y : MulAut W} (hy : y ∈ Y) (v : W) :
    y v * v⁻¹ ∈ commV Y :=
  Subgroup.subset_closure ⟨y, hy, v, rfl⟩

theorem apply_mem_commV {Y : Subgroup (MulAut W)} {y : MulAut W} (hy : y ∈ Y) {u : W}
    (hu : u ∈ commV Y) : y u ∈ commV Y :=
  CFSG.Quasithin.commV_apply_mem_of_mem hy hu

section Cocycle

variable {Y : Subgroup (MulAut W)} (π : ↥(alternatingGroup (Fin 5)) →* ↥Y)
  (β : ↥(commV Y) →* ↥(G6.coreMod 5))

@[expose] noncomputable def cocycle (v : W) (γ : ↥(alternatingGroup (Fin 5))) :
    ↥(G6.coreMod 5) :=
  β ⟨((π γ : ↥Y) : MulAut W) v * v⁻¹, gen_mem_commV (π γ).2 v⟩

theorem cocycle_mul_left (v v' : W) (γ : ↥(alternatingGroup (Fin 5))) :
    cocycle π β (v * v') γ = cocycle π β v γ * cocycle π β v' γ := by
  unfold cocycle
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
  ac_rfl

theorem cocycle_eq_one_of_fix {v : W} {γ : ↥(alternatingGroup (Fin 5))}
    (h : ((π γ : ↥Y) : MulAut W) v = v) : cocycle π β v γ = 1 := by
  unfold cocycle
  have e : (⟨((π γ : ↥Y) : MulAut W) v * v⁻¹, gen_mem_commV (π γ).2 v⟩ :
      ↥(commV Y)) = 1 := Subtype.ext (by simp [h])
  rw [e, map_one]

variable {π β}

theorem mem_fixV_of_cocycle_eq_one (hY : Group.IsPerfect ↥Y) (hπ : Function.Surjective π)
    (hβk : ∀ u : ↥(commV Y), β u = 1 → (u : W) ∈ fixV Y) {v : W}
    (hv : ∀ γ, cocycle π β v γ = 1) : v ∈ fixV Y := by
  have hmem : ∀ y : ↥Y, (y : MulAut W) v * v⁻¹ ∈ fixV Y := by
    intro y
    obtain ⟨γ, rfl⟩ := hπ y
    exact hβk _ (hv γ)
  let f : ↥Y →* ↥(fixV Y) :=
    { toFun := fun y => ⟨(y : MulAut W) v * v⁻¹, hmem y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb := hmem b
        set w := (b : MulAut W) v * v⁻¹ with hw
        have hbw : (b : MulAut W) v = w * v := by rw [hw]; group
        have haw : (a : MulAut W) w = w := hb a a.2
        show ((a * b : ↥Y) : MulAut W) v * v⁻¹ = ((a : MulAut W) v * v⁻¹) * w
        rw [Subgroup.coe_mul, MulAut.mul_apply, hbw, map_mul, haw]
        ac_rfl }
  intro y hy
  have h1 : f ⟨y, hy⟩ = 1 := by
    have htop : commutator ↥Y = ⊤ := Group.isPerfect_def.1 hY
    have hle : commutator ↥Y ≤ f.ker := Abelianization.commutator_subset_ker f
    rw [htop] at hle
    exact hle (Subgroup.mem_top _)
  have h2 : y v * v⁻¹ = 1 := congrArg Subtype.val h1
  exact mul_inv_eq_one.1 h2

variable (hβe : ∀ (γ : ↥(alternatingGroup (Fin 5))) (u : ↥(commV Y))
  (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y),
  β ⟨_, hu⟩ = G6.coreAct 5 (γ : Perm (Fin 5)) (β u))
include hβe

theorem cocycle_mul (v : W) (γ γ' : ↥(alternatingGroup (Fin 5))) :
    cocycle π β v (γ * γ') =
      cocycle π β v γ * G6.coreAct 5 (γ : Perm (Fin 5)) (cocycle π β v γ') := by
  unfold cocycle
  have hu1 : ((π γ : ↥Y) : MulAut W) (((π γ' : ↥Y) : MulAut W) v * v⁻¹) ∈ commV Y :=
    apply_mem_commV (π γ).2 (gen_mem_commV (π γ').2 v)
  have e : (⟨((π (γ * γ') : ↥Y) : MulAut W) v * v⁻¹,
      gen_mem_commV (π (γ * γ')).2 v⟩ : ↥(commV Y)) =
      ⟨_, hu1⟩ * ⟨((π γ : ↥Y) : MulAut W) v * v⁻¹,
        gen_mem_commV (π γ).2 v⟩ := by
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, MulAut.mul_apply, map_inv]
    group
  rw [e, map_mul, hβe γ ⟨_, gen_mem_commV (π γ').2 v⟩ hu1, mul_comm]

theorem cocycle_conj (v : W) (δ γ : ↥(alternatingGroup (Fin 5))) :
    cocycle π β (((π δ : ↥Y) : MulAut W) v) γ =
      G6.coreAct 5 (δ : Perm (Fin 5)) (cocycle π β v (δ⁻¹ * γ * δ)) := by
  unfold cocycle
  have hu1 : ((π δ : ↥Y) : MulAut W) (((π (δ⁻¹ * γ * δ) : ↥Y) : MulAut W) v * v⁻¹) ∈
      commV Y :=
    apply_mem_commV (π δ).2 (gen_mem_commV (π (δ⁻¹ * γ * δ)).2 v)
  have e : (⟨((π γ : ↥Y) : MulAut W) (((π δ : ↥Y) : MulAut W) v) *
      (((π δ : ↥Y) : MulAut W) v)⁻¹, gen_mem_commV (π γ).2 _⟩ :
        ↥(commV Y)) = ⟨_, hu1⟩ := by
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply,
      MulAut.inv_apply, MulEquiv.apply_symm_apply]
  rw [e, hβe δ ⟨_, gen_mem_commV (π (δ⁻¹ * γ * δ)).2 v⟩ hu1]

end Cocycle

theorem eq_of_coboundary_eq {m m' : ↥(G6.coreMod 5)}
    (h : ∀ γ : ↥(alternatingGroup (Fin 5)),
      G6.coreAct 5 (γ : Perm (Fin 5)) m * m⁻¹ = G6.coreAct 5 (γ : Perm (Fin 5)) m' * m'⁻¹) :
    m = m' := by
  have h1 : m * m'⁻¹ = 1 := by
    refine eq_one_of_fixed _ fun γ => ?_
    have h2 := h γ
    rw [map_mul, map_inv]
    have e1 : G6.coreAct 5 (γ : Perm (Fin 5)) m =
        (G6.coreAct 5 (γ : Perm (Fin 5)) m' * m'⁻¹) * m := by
      rw [← h2]
      group
    rw [e1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact mul_inv_eq_one.1 h1

@[expose] def w5c (j : Fin 5) : ↥(G6.coreMod 5) := ⟨Multiplicative.ofAdd (w5 j), w5_sum j⟩

theorem coreAct_w5c (σ : Perm (Fin 5)) (j : Fin 5) : G6.coreAct 5 σ (w5c j) = w5c (σ j) :=
  Subtype.ext (permAct_w5 σ j)

theorem exists_coboundary_klein {Y : Subgroup (MulAut W)} (hY : Group.IsPerfect ↥Y)
    {π : ↥(alternatingGroup (Fin 5)) →* ↥Y} (hs : Function.Surjective π)
    (hinj : Function.Injective π) {β : ↥(commV Y) →* ↥(G6.coreMod 5)}
    (hβk : ∀ u : ↥(commV Y), β u = 1 → (u : W) ∈ fixV Y)
    (hβe : ∀ (γ : ↥(alternatingGroup (Fin 5))) (u : ↥(commV Y))
      (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y),
      β ⟨_, hu⟩ = G6.coreAct 5 (γ : Perm (Fin 5)) (β u))
    {Q : Subgroup (MulAut W)} (hQY : Q ≤ Y) (hQ4 : Nat.card ↥Q = 4) {u : W}
    (hQu : ∀ q ∈ Q, q u = u) (hu : u ∉ fixV Y) :
    ∃ c ∈ alternatingGroup (Fin 5), (∀ δ : ↥(alternatingGroup (Fin 5)),
        ((π δ : ↥Y) : MulAut W) ∈ Q ↔ c * (δ : Perm (Fin 5)) * c⁻¹ ∈ A7.kleinV0) ∧
      ∀ γ, cocycle π β u γ = G6.coreAct 5 (γ : Perm (Fin 5)) (G6.coreAct 5 c⁻¹ (w5c 4)) *
        (G6.coreAct 5 c⁻¹ (w5c 4))⁻¹ := by
  classical
  have hY60 : Nat.card ↥Y = 60 := by
    rw [← Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hs⟩).toEquiv,
      SteinbergCB.nat_card_alternating_five]
  set QA : Subgroup ↥(alternatingGroup (Fin 5)) := (Q.subgroupOf Y).comap π with hQA
  have hQA4 : Nat.card ↥QA = 4 := by
    have h1 : QA.map π = Q.subgroupOf Y := Subgroup.map_comap_eq_self_of_surjective hs _
    have h2 := Subgroup.card_map_of_injective (K := QA) hinj
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQY).toEquiv, hQ4] at h2
    exact h2.symm
  have hidx : QA.index = 15 := by
    have h := QA.index_mul_card
    rw [hQA4, SteinbergCB.nat_card_alternating_five] at h
    omega
  obtain ⟨m₀, hm₀⟩ := exists_coboundary_of_odd_index coreMod_sq
    ((G6.coreAct 5).comp (alternatingGroup (Fin 5)).subtype) (f := cocycle π β u)
    (fun g h => cocycle_mul hβe u g h) (P := QA) (by rw [hidx]; decide)
    (fun δ hδ => cocycle_eq_one_of_fix π β (hQu _ hδ))
  have hm₀Q : ∀ δ ∈ QA, G6.coreAct 5 (δ : Perm (Fin 5)) m₀ = m₀ := by
    intro δ hδ
    have h := hm₀ δ
    rw [cocycle_eq_one_of_fix π β (hQu _ hδ)] at h
    exact (mul_inv_eq_one.1 h.symm)
  have hm₀1 : m₀ ≠ 1 := by
    intro h1
    apply hu
    refine mem_fixV_of_cocycle_eq_one hY hs hβk fun γ => ?_
    rw [hm₀, h1, map_one, mul_inv_cancel]
  set S : Subgroup (Perm (Fin 5)) := QA.map (alternatingGroup (Fin 5)).subtype with hS
  have hSA : S ≤ alternatingGroup (Fin 5) := fun x ⟨y, _, hy⟩ => hy ▸ y.2
  have hS4 : Nat.card ↥S = 4 := by
    rw [hS, Subgroup.card_map_of_injective (alternatingGroup (Fin 5)).subtype_injective, hQA4]
  obtain ⟨c, hcA, hc⟩ := A7.exists_conj_kleinV0 hSA hS4
  have hmemS : ∀ δ : ↥(alternatingGroup (Fin 5)), δ ∈ QA ↔ (δ : Perm (Fin 5)) ∈ S := by
    intro δ
    constructor
    · intro h
      exact ⟨δ, h, rfl⟩
    · rintro ⟨δ', hδ', h⟩
      have : δ' = δ := Subtype.ext h
      rwa [← this]
  refine ⟨c, hcA, fun δ => ?_, fun γ => ?_⟩
  · rw [← hc, ← hmemS]
    rfl
  have hfixV0 : ∀ b ∈ A7.kleinV0Set, ∀ i,
      Multiplicative.toAdd ((G6.coreAct 5 c m₀ : ↥(G6.coreMod 5)) : G6.PermMod 5) (b⁻¹ i) =
        Multiplicative.toAdd ((G6.coreAct 5 c m₀ : ↥(G6.coreMod 5)) : G6.PermMod 5) i := by
    intro b hb i
    have hbA : b ∈ alternatingGroup (Fin 5) := A7.kleinV0_le_alternating hb
    set s : ↥(alternatingGroup (Fin 5)) := ⟨c⁻¹ * b * c,
      (alternatingGroup (Fin 5)).mul_mem ((alternatingGroup (Fin 5)).mul_mem
        ((alternatingGroup (Fin 5)).inv_mem hcA) hbA) hcA⟩ with hsdef
    have hs' : s ∈ QA := by
      rw [hmemS, hc]
      show c * (c⁻¹ * b * c) * c⁻¹ ∈ A7.kleinV0
      rw [show c * (c⁻¹ * b * c) * c⁻¹ = b by group]
      exact hb
    have h1 := hm₀Q s hs'
    have h2 : G6.coreAct 5 b (G6.coreAct 5 c m₀) = G6.coreAct 5 c m₀ := by
      rw [← MulAut.mul_apply, ← map_mul, show b * c = c * (c⁻¹ * b * c) by group, map_mul,
        MulAut.mul_apply]
      exact congrArg _ h1
    have h3 := congrFun (congrArg Multiplicative.toAdd (congrArg Subtype.val h2)) i
    exact h3
  rcases kleinV0_fixed _ (G6.coreAct 5 c m₀).2 hfixV0 with h0 | h4
  · exfalso
    apply hm₀1
    have h5 : G6.coreAct 5 c m₀ = 1 := Subtype.ext (Multiplicative.toAdd.injective h0)
    rw [MulEquiv.map_eq_one_iff] at h5
    exact h5
  · have h5 : G6.coreAct 5 c m₀ = w5c 4 := Subtype.ext (Multiplicative.toAdd.injective h4)
    have h6 : m₀ = G6.coreAct 5 c⁻¹ (w5c 4) := by
      rw [← h5, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hm₀, h6]
    rfl

theorem coreAct_conj (s γ : ↥(alternatingGroup (Fin 5))) (x : ↥(G6.coreMod 5)) :
    G6.coreAct 5 (s : Perm (Fin 5)) (G6.coreAct 5 ((s⁻¹ * γ * s : ↥(alternatingGroup (Fin 5))) :
      Perm (Fin 5)) x) = G6.coreAct 5 (γ : Perm (Fin 5)) (G6.coreAct 5 (s : Perm (Fin 5)) x) := by
  rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
  congr 2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem false_of_altDn5 {Y : Subgroup (MulAut W)}
    (hY : Group.IsPerfect ↥Y) {π : ↥(alternatingGroup (Fin 5)) →* ↥Y}
    (hπ : (FFModel.altDn 5).RealizesVia Y (commV Y) (fixV Y ⊓ commV Y) π)
    {a : MulAut W} (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y)
    {P : Subgroup (MulAut W)} (hPY : P ≤ Y) (hP2 : IsPGroup 2 ↥P)
    (hPodd : Odd (P.subgroupOf Y).index) {v₂ : W} (hPv : ∀ p ∈ P, p v₂ = v₂)
    (hPa : ∀ p ∈ P, p (a v₂) = a v₂ ∨ p (a v₂) = v₂ * a v₂)
    (ha2 : a (a v₂) = v₂ * a v₂) (hv : v₂ ∉ fixV Y) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hs, -, β, -, hβk, hβe⟩ := altRealizes_clean hπ
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.altDn_faithful (le_refl 5)) hπ
  have hβk' : ∀ u : ↥(commV Y), β u = 1 → (u : W) ∈ fixV Y := fun u hu => ((hβk u).1 hu).1
  have hY60 : Nat.card ↥Y = 60 := by
    rw [← Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hs⟩).toEquiv,
      SteinbergCB.nat_card_alternating_five]
  have : Finite ↥Y := Finite.of_surjective π hs
  have : Finite ↥P :=
    Finite.of_injective (Subgroup.inclusion hPY) (Subgroup.inclusion_injective hPY)
  have hP4 : Nat.card ↥P = 4 := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    have h := (P.subgroupOf Y).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv, hk, hY60] at h
    obtain ⟨r, hr⟩ := hPodd
    rw [hr] at h
    have hk6 : k < 6 := by
      by_contra hk6
      have h1 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2' : 2 ^ k ≤ 60 := by
        rw [← h]
        exact Nat.le_mul_of_pos_left _ (by omega)
      omega
    rw [hk]
    interval_cases k <;> norm_num at h ⊢ <;> omega
  set Pa : Subgroup (MulAut W) := P.map (MulAut.conj a).toMonoidHom with hPadef
  have hPaY : Pa ≤ Y := by
    rintro _ ⟨p, hp, rfl⟩
    exact haY p (hPY hp)
  have hPa4 : Nat.card ↥Pa = 4 := by
    rw [hPadef, Subgroup.card_map_of_injective (MulAut.conj a).injective, hP4]
  have hPau : ∀ q ∈ Pa, q (a v₂) = a v₂ := by
    rintro _ ⟨p, hp, rfl⟩
    show (a * p * a⁻¹) (a v₂) = a v₂
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hPv p hp]
  have hinvfix : ∀ w ∈ fixV Y, a⁻¹ w ∈ fixV Y := by
    intro w hw y hy
    have h1 := hw _ (haY y hy)
    calc y (a⁻¹ w) = a⁻¹ ((a * y * a⁻¹) w) := by
          rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      _ = a⁻¹ w := by rw [h1]
  have hav : a v₂ ∉ fixV Y := fun h => hv (by simpa using hinvfix _ h)
  obtain ⟨c₁, hc₁A, hc₁, hcoc₁⟩ := exists_coboundary_klein hY hs hinj hβk' hβe hPY hP4 hPv hv
  obtain ⟨c₂, -, -, hcoc₂⟩ := exists_coboundary_klein hY hs hinj hβk' hβe hPaY hPa4 hPau hav
  obtain ⟨m₁, hm₁⟩ : ∃ m, m = G6.coreAct 5 c₁⁻¹ (w5c 4) := ⟨_, rfl⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m, m = G6.coreAct 5 c₂⁻¹ (w5c 4) := ⟨_, rfl⟩
  rw [← hm₁] at hcoc₁
  rw [← hm₂] at hcoc₂
  have hc₁m₁ : G6.coreAct 5 c₁ m₁ = w5c 4 := by
    rw [hm₁, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hmove : ∀ b ∈ A7.kleinV0Set,
      G6.coreAct 5 b (G6.coreAct 5 c₁ m₂) = G6.coreAct 5 c₁ m₂ ∨
        G6.coreAct 5 b (G6.coreAct 5 c₁ m₂) = w5c 4 * G6.coreAct 5 c₁ m₂ := by
    intro b hb
    have hbA : b ∈ alternatingGroup (Fin 5) := A7.kleinV0_le_alternating hb
    set sp : ↥(alternatingGroup (Fin 5)) := ⟨c₁⁻¹ * b * c₁,
      (alternatingGroup (Fin 5)).mul_mem ((alternatingGroup (Fin 5)).mul_mem
        ((alternatingGroup (Fin 5)).inv_mem hc₁A) hbA) hc₁A⟩ with hspdef
    have hsP : ((π sp : ↥Y) : MulAut W) ∈ P := by
      rw [hc₁]
      show c₁ * (c₁⁻¹ * b * c₁) * c₁⁻¹ ∈ A7.kleinV0
      rw [show c₁ * (c₁⁻¹ * b * c₁) * c₁⁻¹ = b by group]
      exact hb
    have hbc : b * c₁ = c₁ * (sp : Perm (Fin 5)) := by
      show b * c₁ = c₁ * (c₁⁻¹ * b * c₁)
      group
    have hb1 : G6.coreAct 5 b (G6.coreAct 5 c₁ m₂) =
        G6.coreAct 5 c₁ (G6.coreAct 5 (sp : Perm (Fin 5)) m₂) := by
      rw [← MulAut.mul_apply, ← map_mul, hbc, map_mul, MulAut.mul_apply]
    have hcs : ∀ γ, cocycle π β (((π sp : ↥Y) : MulAut W) (a v₂)) γ =
        G6.coreAct 5 (γ : Perm (Fin 5)) (G6.coreAct 5 (sp : Perm (Fin 5)) m₂) *
          (G6.coreAct 5 (sp : Perm (Fin 5)) m₂)⁻¹ := by
      intro γ
      rw [cocycle_conj hβe, hcoc₂, map_mul, map_inv, coreAct_conj]
    rcases hPa _ hsP with h | h
    · left
      have h3 : G6.coreAct 5 (sp : Perm (Fin 5)) m₂ = m₂ := by
        refine eq_of_coboundary_eq fun γ => ?_
        rw [← hcs, h, hcoc₂]
      rw [hb1, h3]
    · right
      have h3 : G6.coreAct 5 (sp : Perm (Fin 5)) m₂ = m₁ * m₂ := by
        refine eq_of_coboundary_eq fun γ => ?_
        rw [← hcs, h, cocycle_mul_left, hcoc₁, hcoc₂, map_mul, mul_inv_rev]
        ac_rfl
      rw [hb1, h3, map_mul, hc₁m₁]
  have hj : G6.coreAct 5 c₁ m₂ = w5c ((c₁ * c₂⁻¹) 4) := by
    rw [hm₂, ← MulAut.mul_apply, ← map_mul, coreAct_w5c]
  have hj4 : (c₁ * c₂⁻¹) 4 = 4 := by
    refine kleinV0_moved _ fun b hb => ?_
    rcases hmove b hb with h | h
    · left
      rw [hj, coreAct_w5c] at h
      funext i
      exact congrFun (congrArg (fun x : ↥(G6.coreMod 5) =>
        Multiplicative.toAdd ((x : G6.PermMod 5))) (h.symm.trans (coreAct_w5c b _).symm)).symm i
    · right
      rw [hj] at h
      funext i
      have h' := congrFun (congrArg (fun x : ↥(G6.coreMod 5) =>
        Multiplicative.toAdd ((x : G6.PermMod 5))) h) i
      exact h'
  have hm : m₂ = m₁ := by
    have h1 : G6.coreAct 5 c₁ m₂ = G6.coreAct 5 c₁ m₁ := by rw [hj, hj4, hc₁m₁]
    exact (G6.coreAct 5 c₁).injective h1
  have hcoc : ∀ γ, cocycle π β (v₂ * a v₂) γ = 1 := by
    intro γ
    rw [cocycle_mul_left, hcoc₁, hcoc₂, ← hm]
    exact coreMod_sq _
  have h3 := mem_fixV_of_cocycle_eq_one hY hs hβk' hcoc
  rw [← ha2] at h3
  have h4 := hinvfix _ (hinvfix _ h3)
  rw [MulAut.inv_apply_self, MulAut.inv_apply_self] at h4
  exact hv h4

end A6L76Oe

end CFSG.Quasithin.H13.A6
