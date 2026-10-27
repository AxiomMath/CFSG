module

public import CFSG.Quasithin.Vol2.Ch3B513NAltA
public import CFSG.Quasithin.Background.B3ThreeCoh
public import CFSG.Quasithin.Background.C124YZActOdd
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Module

variable {n : ℕ}

@[expose] noncomputable def coreActAlt (n : ℕ) : B3.LG n →* MulAut ↥(G6.coreMod n) :=
  (G6.coreAct n).comp (alternatingGroup (Fin n)).subtype

theorem esub_subgroupOf_eq_bot (hn : Odd n) : (B3.Esub n).subgroupOf (B3.U0 n) = ⊥ := by
  rw [← B513N.map_coreEquiv_ker, C124.YZ.natKer_odd hn, Subgroup.bot_subgroupOf,
    Subgroup.map_bot]

@[expose] noncomputable def coreSecHom (n : ℕ) : ↥(G6.coreMod n) →* B3.Mod.V n B3.Mod.ut0 :=
  (QuotientGroup.mk' ((B3.Esub n).subgroupOf (B3.U0 n))).comp B513N.coreEquiv.toMonoidHom

theorem coreSecHom_bijective (hn : Odd n) : Function.Bijective (coreSecHom n) := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : B513N.coreEquiv x ∈ (B3.Esub n).subgroupOf (B3.U0 n) :=
      (QuotientGroup.eq_one_iff _).1 hx
    rw [esub_subgroupOf_eq_bot hn, Subgroup.mem_bot] at h1
    exact (MulEquiv.map_eq_one_iff _).1 h1
  · exact (QuotientGroup.mk'_surjective ((B3.Esub n).subgroupOf (B3.U0 n))).comp
      B513N.coreEquiv.surjective

theorem zeroClass_coreActAlt (hn : n = 5 ∨ n = 7) :
    @B3.ZeroClass _ _ ↥(G6.coreMod n) (Subgroup.toCommGroup _) (coreActAlt n) := by
  let _ : CommGroup ↥(G6.coreMod n) := Subgroup.toCommGroup _
  have hodd : Odd n := by rcases hn with rfl | rfl <;> decide
  let e : ↥(G6.coreMod n) ≃* B3.Mod.V n B3.Mod.ut0 :=
    MulEquiv.ofBijective (coreSecHom n) (coreSecHom_bijective hodd)
  have he : B3.IsModIso (coreActAlt n) (B3.actL n B3.Mod.ut0) e := fun _ _ => rfl
  exact he.symm.zeroClass (B3.H1_natural_odd hn)

end Module

section Split

variable {G : Type} [Group G] [Finite G] {X L : Subgroup G}

theorem commutator_mem_blockU_of_mem_pCoreOf (hL : IsShort2 L) (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) {q l : G} (hq : q ∈ pCoreOf 2 X) (hl : l ∈ L) :
    q * l * q⁻¹ * l⁻¹ ∈ blockU L :=
  C1.commutator_mem_blockU_of_mem_blockQ hL
    (fun _ hl' => C1.commutator_mem_blockQ_of_mem_pCoreOf hLX hXL hq hl') l hl

theorem conj_mem_blockQ' {l m : G} (hl : l ∈ L) (hm : m ∈ blockQ L) :
    l * m * l⁻¹ ∈ blockQ L :=
  (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockQ L hl) m).mp hm

theorem conj_mem_blockU' {l u : G} (hl : l ∈ L) (hu : u ∈ blockU L) :
    l * u * l⁻¹ ∈ blockU L :=
  (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L hl) u).mp hu

theorem blockU_le_pCoreOf' (hL : IsShort2 L) (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) : blockU L ≤ pCoreOf 2 X :=
  (C1.blockU_le_blockQ hL).trans (C1.le_pCoreOf_of_normalized ((C1.blockQ_le L).trans hLX)
    (fun _ hg => C1.mem_normalizer_blockQ (hXL hg)) (C1.blockQ_isPGroup L))

theorem comm_blockQ_of_blockZ_eq_bot (hL : IsShort2 L) (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hZ : blockZ L = ⊥)
    (hQU : ∀ q ∈ pCoreOf 2 X, ∀ u ∈ blockU L, q * u = u * q) {q m : G}
    (hq : q ∈ pCoreOf 2 X) (hm : m ∈ blockQ L) : q * m = m * q := by
  have hmL : m ∈ L := C1.blockQ_le L hm
  have hab := (C1.elemAb2_blockU hL).1
  set e : G := q * m * q⁻¹ * m⁻¹ with he
  have heU : e ∈ blockU L := commutator_mem_blockU_of_mem_pCoreOf hL hLX hXL hq hmL
  have hcent : ∀ ℓ ∈ L, ℓ * e * ℓ⁻¹ = e := by
    intro ℓ hℓ
    set c : G := q * ℓ * q⁻¹ * ℓ⁻¹ with hc
    have hcU : c ∈ blockU L := commutator_mem_blockU_of_mem_pCoreOf hL hLX hXL hq hℓ
    set m' : G := ℓ * m * ℓ⁻¹ with hm'
    have hm'Q : m' ∈ blockQ L := conj_mem_blockQ' hℓ hm
    set w : G := ℓ * e * ℓ⁻¹ with hw
    have hwU : w ∈ blockU L := conj_mem_blockU' hℓ heU
    set u₁ : G := ℓ * m * ℓ⁻¹ * m⁻¹ with hu₁
    have hu₁U : u₁ ∈ blockU L := C1.commutator_mem_blockU' hℓ hm
    have h1 : q * ℓ * q⁻¹ = c * ℓ := by
      rw [hc]
      group
    have h2 : q * m * q⁻¹ = e * m := by
      rw [he]
      group
    have hcw : c * w = w * c := hab c hcU w hwU
    have hcm : c * m' = m' * c := C1.blockU_comm hL c hcU m' hm'Q
    have h3 : q * m' * q⁻¹ = w * m' := by
      calc q * m' * q⁻¹ = (q * ℓ * q⁻¹) * (q * m * q⁻¹) * (q * ℓ * q⁻¹)⁻¹ := by
            rw [hm']
            group
        _ = (c * ℓ) * (e * m) * (c * ℓ)⁻¹ := by rw [h1, h2]
        _ = c * (ℓ * e * ℓ⁻¹) * (ℓ * m * ℓ⁻¹) * c⁻¹ := by group
        _ = c * w * m' * c⁻¹ := rfl
        _ = w * m' := by
          rw [hcw, mul_assoc w c m', hcm]
          group
    have hmu : m' = u₁ * m := by
      rw [hm', hu₁]
      group
    have hq1 : q * u₁ * q⁻¹ = u₁ := by
      rw [hQU q hq u₁ hu₁U]
      group
    have h4 : q * m' * q⁻¹ = u₁ * e * m := by
      calc q * m' * q⁻¹ = (q * u₁ * q⁻¹) * (q * m * q⁻¹) := by
            rw [hmu]
            group
        _ = u₁ * (e * m) := by rw [hq1, h2]
        _ = u₁ * e * m := by group
    have h5 : w * (u₁ * m) = u₁ * e * m := by rw [← hmu, ← h3, h4]
    have h6 : w * u₁ = u₁ * e := by
      rw [← mul_assoc] at h5
      exact mul_right_cancel h5
    rw [hab w hwU u₁ hu₁U] at h6
    exact mul_left_cancel h6
  have hZe : e ∈ blockZ L := ⟨heU, Subgroup.mem_centralizer_iff.2 fun ℓ hℓ => by
    calc ℓ * e = (ℓ * e * ℓ⁻¹) * ℓ := by group
      _ = e * ℓ := by rw [hcent ℓ hℓ]⟩
  rw [hZ, Subgroup.mem_bot] at hZe
  calc q * m = (q * m * q⁻¹ * m⁻¹) * (m * q) := by group
    _ = m * q := by rw [← he, hZe, one_mul]

theorem pCoreOf_le_blockU_sup {n : ℕ} (hn : n = 5 ∨ n = 7) (hL : IsShort2 L) (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hZ : blockZ L = ⊥)
    (hQU : ∀ q ∈ pCoreOf 2 X, ∀ u ∈ blockU L, q * u = u * q)
    (ρ : ↥L →* B3.LG n) (hρ : Function.Surjective ρ)
    (hker : ∀ l : ↥L, ρ l = 1 → (l : G) ∈ blockQ L)
    (θ : ↥(blockU L) ≃* ↥(G6.coreMod n))
    (hθ : ∀ (l : ↥L) (u v : ↥(blockU L)), (v : G) = l * u * l⁻¹ →
      θ v = G6.coreAct n (ρ l) (θ u)) :
    pCoreOf 2 X ≤ blockU L ⊔ (pCoreOf 2 X ⊓ Subgroup.centralizer (L : Set G)) := by
  classical
  let _ : CommGroup ↥(G6.coreMod n) := Subgroup.toCommGroup _
  intro x hx
  have hcU : ∀ l : ↥L, x * l * x⁻¹ * (l : G)⁻¹ ∈ blockU L := fun l =>
    commutator_mem_blockU_of_mem_pCoreOf hL hLX hXL hx l.2
  let c : ↥L → ↥(blockU L) := fun l => ⟨_, hcU l⟩
  have hconj : ∀ (l : ↥L) (u : ↥(blockU L)), (l : G) * u * (l : G)⁻¹ ∈ blockU L :=
    fun l u => conj_mem_blockU' l.2 u.2
  have hcmul : ∀ a b : ↥L, c (a * b) = c a * ⟨_, hconj a (c b)⟩ := by
    intro a b
    apply Subtype.ext
    show x * ((a : G) * b) * x⁻¹ * ((a : G) * b)⁻¹ =
      (x * a * x⁻¹ * (a : G)⁻¹) * ((a : G) * (x * b * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹)
    group
  have hc1 : ∀ m : ↥L, ρ m = 1 → c m = 1 := by
    intro m hm
    apply Subtype.ext
    show x * m * x⁻¹ * (m : G)⁻¹ = 1
    rw [comm_blockQ_of_blockZ_eq_bot hL hLX hXL hZ hQU hx (hker m hm)]
    group
  have hcfib : ∀ a b : ↥L, ρ a = ρ b → c a = c b := by
    intro a b hab
    have hm : ρ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have hb : b = a * (a⁻¹ * b) := by group
    rw [hb, hcmul, hc1 _ hm]
    apply Subtype.ext
    show (c a : G) = (c a : G) * ((a : G) * 1 * (a : G)⁻¹)
    group
  choose s hs using hρ
  let d : B3.LG n → ↥(G6.coreMod n) := fun σ => θ (c (s σ))
  have hd : B3.IsDer (coreActAlt n) d := by
    intro σ τ
    have h1 : c (s (σ * τ)) = c (s σ * s τ) := hcfib _ _ (by rw [map_mul, hs, hs, hs])
    show θ (c (s (σ * τ))) = θ (c (s σ)) * coreActAlt n σ (θ (c (s τ)))
    rw [h1, hcmul, map_mul, hθ (s σ) (c (s τ)) ⟨_, hconj (s σ) (c (s τ))⟩ rfl, hs]
    rfl
  obtain ⟨v, hv⟩ := zeroClass_coreActAlt hn d hd
  set u₀ : ↥(blockU L) := θ.symm v with hu₀
  have key : ∀ l : ↥L, (c l : G) = l * u₀ * (l : G)⁻¹ * (u₀ : G)⁻¹ := by
    intro l
    have h1 : c l = c (s (ρ l)) := hcfib _ _ (hs _).symm
    have h2 : θ (c (s (ρ l))) = coreActAlt n (ρ l) v * v⁻¹ := congrFun hv (ρ l)
    have h3 : θ ⟨_, hconj l u₀⟩ = coreActAlt n (ρ l) v := by
      rw [hθ l u₀ _ rfl, hu₀, MulEquiv.apply_symm_apply]
      rfl
    have h4 : c l = ⟨_, hconj l u₀⟩ * u₀⁻¹ := by
      apply θ.injective
      rw [h1, h2, map_mul, map_inv, h3, hu₀, MulEquiv.apply_symm_apply]
      rfl
    rw [h4]
    rfl
  have hu₀X : (u₀ : G) ∈ pCoreOf 2 X := blockU_le_pCoreOf' hL hLX hXL u₀.2
  have hu₀sq : (u₀ : G) * u₀ = 1 := by
    have := (C1.elemAb2_blockU hL).2 u₀ u₀.2
    rwa [pow_two] at this
  have hu₀inv : (u₀ : G)⁻¹ = u₀ := inv_eq_of_mul_eq_one_right hu₀sq
  have hyC : (u₀ : G)⁻¹ * x ∈ Subgroup.centralizer (L : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
    have hk := key ⟨l, hl⟩
    have hxl : x * l = (l * u₀ * l⁻¹ * (u₀ : G)⁻¹) * l * x := by
      rw [← hk]
      show x * l = (x * l * x⁻¹ * l⁻¹) * l * x
      group
    have ha : l * (u₀ : G) * l⁻¹ ∈ blockU L := conj_mem_blockU' hl u₀.2
    have hcomm : (u₀ : G) * (l * u₀ * l⁻¹) = (l * u₀ * l⁻¹) * u₀ :=
      (C1.elemAb2_blockU hL).1 _ u₀.2 _ ha
    rw [hu₀inv] at hxl ⊢
    calc l * ((u₀ : G) * x) = l * u₀ * x := by group
      _ = (l * u₀ * l⁻¹) * l * x := by group
      _ = (u₀ : G) * (u₀ * (l * u₀ * l⁻¹)) * l * x := by
          rw [← mul_assoc (u₀ : G) u₀, hu₀sq, one_mul]
      _ = (u₀ : G) * ((l * u₀ * l⁻¹) * u₀) * l * x := by rw [hcomm]
      _ = (u₀ : G) * ((l * u₀ * l⁻¹ * u₀) * l * x) := by group
      _ = (u₀ : G) * (x * l) := by rw [hxl]
      _ = (u₀ : G) * x * l := by group
  have hyX : (u₀ : G)⁻¹ * x ∈ pCoreOf 2 X := mul_mem (inv_mem hu₀X) hx
  have hx' : x = (u₀ : G) * ((u₀ : G)⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem_sup u₀.2 ⟨hyX, hyC⟩

end Split

end CFSG.Quasithin.SmithC27
