module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectVZ
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectNat
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectZero

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V H B D D₃ Z₁ : Subgroup G} {n : ℕ}

theorem mem_sup_of_comm_decomp {W₁ W₂ : Subgroup G}
    (hc : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a) {x : G} (hx : x ∈ W₁ ⊔ W₂) :
    ∃ a ∈ W₁, ∃ b ∈ W₂, a * b = x := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ W₁, ∃ b ∈ W₂, a * b = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', W₁.mul_mem ha ha', b * b', W₂.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [hc a' ha' b hb]
          _ = a * b * (a' * b') := by group
      one_mem' := ⟨1, W₁.one_mem, 1, W₂.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, W₁.inv_mem ha, b⁻¹, W₂.inv_mem hb, ?_⟩
        exact (hc a⁻¹ (W₁.inv_mem ha) b⁻¹ (W₂.inv_mem hb)).trans (mul_inv_rev a b).symm }
  have hle : W₁ ⊔ W₂ ≤ P :=
    sup_le (fun a ha => ⟨a, ha, 1, W₂.one_mem, mul_one a⟩)
      (fun b hb => ⟨1, W₁.one_mem, b, hb, one_mul b⟩)
  obtain ⟨a, ha, b, hb, h⟩ := hle hx
  exact ⟨a, ha, b, hb, h⟩

theorem conj_mem_commVL' {VZ : Subgroup G} {ℓ : G} (hVZ : ℓ ∈ Subgroup.normalizer (VZ : Set G))
    (hL : ℓ ∈ Subgroup.normalizer (L : Set G)) {y : G} (hy : y ∈ ⁅VZ, L⁆) :
    ℓ * y * ℓ⁻¹ ∈ ⁅VZ, L⁆ := by
  have key : ⁅VZ, L⁆ ≤ ⁅VZ, L⁆.comap (MulAut.conj ℓ).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    show ℓ * (x * l * x⁻¹ * l⁻¹) * ℓ⁻¹ ∈ ⁅VZ, L⁆
    have e : ℓ * (x * l * x⁻¹ * l⁻¹) * ℓ⁻¹ =
        (ℓ * x * ℓ⁻¹) * (ℓ * l * ℓ⁻¹) * (ℓ * x * ℓ⁻¹)⁻¹ * (ℓ * l * ℓ⁻¹)⁻¹ := by
      group
    rw [e]
    exact mul_comm_mem_commutator ((Subgroup.mem_normalizer_iff.mp hVZ x).mp hx)
      ((Subgroup.mem_normalizer_iff.mp hL l).mp hl)
  exact key hy

theorem normalizer_conjClosure_of_centralizes (K : Subgroup G) {t : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) (htK : ∀ k ∈ K, t * k * t⁻¹ = k) :
    t ∈ Subgroup.normalizer (conjClosure K L : Set G) := by
  have fwd : ∀ s : G, s ∈ Subgroup.normalizer (L : Set G) → (∀ k ∈ K, s * k * s⁻¹ = k) →
      ∀ x ∈ conjClosure K L, s * x * s⁻¹ ∈ conjClosure K L := by
    intro s hs hsK
    have hgen : conjClosure K L ≤ (conjClosure K L).comap (MulAut.conj s).toMonoidHom := by
      refine conjClosure_le fun g hg k hk => ?_
      show s * (g * k * g⁻¹) * s⁻¹ ∈ conjClosure K L
      have e : s * (g * k * g⁻¹) * s⁻¹ = (s * g * s⁻¹) * k * (s * g * s⁻¹)⁻¹ := by
        have := hsK k hk
        calc s * (g * k * g⁻¹) * s⁻¹ = (s * g * s⁻¹) * (s * k * s⁻¹) * (s * g * s⁻¹)⁻¹ := by group
          _ = (s * g * s⁻¹) * k * (s * g * s⁻¹)⁻¹ := by rw [this]
      rw [e]
      have hg' : s * g * s⁻¹ ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp hs g).mp hg
        exact this
      exact mem_conjClosure hg' hk
    intro x hx
    exact hgen hx
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => fwd t ht htK x hx, fun hx => ?_⟩
  have h := fwd t⁻¹ (Subgroup.inv_mem _ ht) (fun k hk => by
    have h1 := htK k hk
    have hc : t * k = k * t := by
      calc t * k = (t * k * t⁻¹) * t := by group
        _ = k * t := by rw [h1]
    calc t⁻¹ * k * t⁻¹⁻¹ = t⁻¹ * (k * t) := by group
      _ = t⁻¹ * (t * k) := by rw [hc]
      _ = k := by group) _ hx
  have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
  rwa [e] at h

theorem normalizes_of_irreducible {N : Subgroup G} {z : G} (hz : z ∈ N) (hz1 : z ≠ 1)
    (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (hirr : ∀ X : Subgroup G, X ≤ N → L ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = N)
    {t : G} (ht : t ∈ Subgroup.normalizer (L : Set G)) (htz : t * z * t⁻¹ = z) :
    t ∈ Subgroup.normalizer (N : Set G) := by
  have hzp : ∀ k ∈ Subgroup.zpowers z, t * k * t⁻¹ = k := by
    intro k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    rw [← conj_zpow, htz]
  have hsub : conjClosure (Subgroup.zpowers z) L ≤ N := by
    refine conjClosure_le fun g hg k hk => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (Subgroup.mem_normalizer_iff.mp (hLN hg) _).mp (N.zpow_mem hz m)
  have hne : conjClosure (Subgroup.zpowers z) L ≠ ⊥ := by
    intro hb
    apply hz1
    have : z ∈ conjClosure (Subgroup.zpowers z) L := le_conjClosure _ L (Subgroup.mem_zpowers z)
    rw [hb, Subgroup.mem_bot] at this
    exact this
  have hY : conjClosure (Subgroup.zpowers z) L = N := by
    rcases hirr _ hsub (le_normalizer_conjClosure _ L) with h | h
    · exact absurd h hne
    · exact h
  rw [← hY]
  exact normalizer_conjClosure_of_centralizes (Subgroup.zpowers z) ht hzp

theorem commVL_le_VZ {VZ : Subgroup G} (hVZ : ∀ ℓ ∈ L, ∀ x ∈ VZ, ℓ * x * ℓ⁻¹ ∈ VZ) :
    ⁅VZ, L⁆ ≤ VZ := by
  rw [Subgroup.commutator_le]
  intro x hx l hl
  rw [commutatorElement_def]
  have := VZ.mul_mem hx (hVZ l hl x⁻¹ (VZ.inv_mem hx))
  simpa [mul_assoc] using this

theorem le_normalizer_inf_centralizer_nat {W : Subgroup G} (hW : IsNatModCh5 L W n) :
    L ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ L → ∀ x ∈ L ⊓ Subgroup.centralizer (W : Set G),
      g * x * g⁻¹ ∈ L ⊓ Subgroup.centralizer (W : Set G) := by
    intro g hg x hx
    refine ⟨L.mul_mem (L.mul_mem hg hx.1) (L.inv_mem hg), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro w hw
    have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hW.1 (L.inv_mem hg)) w).mp hw
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hw'
    calc w * (g * x * g⁻¹) = g * (g⁻¹ * w * g⁻¹⁻¹ * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * w * g⁻¹⁻¹)) * g⁻¹ := by rw [hc]
      _ = (g * x * g⁻¹) * w := by group
  intro ℓ hℓ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key ℓ hℓ x
  · intro hx
    have := key ℓ⁻¹ (L.inv_mem hℓ) _ hx
    simpa [mul_assoc] using this

theorem centralizer_inf_eq_pCoreOf (h : Hyp5_1_14 G T M L V H B D n) (h5114 : Stmt5_1_14_first)
    {W : Subgroup G} (hW : IsNatModCh5 L W n)
    (hWV : W ≤ conjClosure (quasithinOmegaOneCenter T) L) :
    L ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 L := by
  have hh := h.hyp.toHyp5_0_1
  rcases hh.le_pCoreOf_or_eq inf_le_left (le_normalizer_inf_centralizer_nat hW) with hle | heq
  · apply le_antisymm hle
    refine le_inf (pCoreOf_le 2 L) ?_
    exact (pCoreOf_le_centralizer_VZ h h5114).trans (Subgroup.centralizer_le hWV)
  · exfalso
    apply hW.not_le_centralizer
    exact inf_eq_left.mp heq

theorem ker_eq_of_natural (h : Hyp5_1_14 G T M L V H B D n) (h5114 : Stmt5_1_14_first)
    {W₁ W₂ : Subgroup G} (hW₁ : IsNatModCh5 L W₁ n) (hW₂ : IsNatModCh5 L W₂ n)
    (hV₁ : W₁ ≤ conjClosure (quasithinOmegaOneCenter T) L)
    (hV₂ : W₂ ≤ conjClosure (quasithinOmegaOneCenter T) L) :
    ∀ ℓ ∈ L, ℓ ∈ Subgroup.centralizer (W₁ : Set G) ↔ ℓ ∈ Subgroup.centralizer (W₂ : Set G) := by
  intro ℓ hℓ
  have e1 := centralizer_inf_eq_pCoreOf h h5114 hW₁ hV₁
  have e2 := centralizer_inf_eq_pCoreOf h h5114 hW₂ hV₂
  constructor
  · intro h1
    have h3 : ℓ ∈ L ⊓ Subgroup.centralizer (W₁ : Set G) := ⟨hℓ, h1⟩
    rw [e1] at h3
    rw [← e2] at h3
    exact h3.2
  · intro h1
    have h3 : ℓ ∈ L ⊓ Subgroup.centralizer (W₂ : Set G) := ⟨hℓ, h1⟩
    rw [e2] at h3
    rw [← e1] at h3
    exact h3.2

theorem mem_centralizer_of_mul {S W₁ W₂ : Subgroup G}
    (hS₁ : ∀ s ∈ S, ∀ a ∈ W₁, s * a * s⁻¹ ∈ W₁) (hS₂ : ∀ s ∈ S, ∀ b ∈ W₂, s * b * s⁻¹ ∈ W₂)
    (hsum : W₁ ⊓ W₂ = ⊥) {a b : G} (ha : a ∈ W₁) (hb : b ∈ W₂)
    (hab : a * b ∈ Subgroup.centralizer (S : Set G)) : a ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hab ⊢
  intro s hs
  have hc := hab s hs
  have hu : a⁻¹ * (s * a * s⁻¹) ∈ W₁ := W₁.mul_mem (W₁.inv_mem ha) (hS₁ s hs a ha)
  have hv : b * (s * b * s⁻¹)⁻¹ ∈ W₂ := W₂.mul_mem hb (W₂.inv_mem (hS₂ s hs b hb))
  have huv : a⁻¹ * (s * a * s⁻¹) = b * (s * b * s⁻¹)⁻¹ := by
    have e : s * a * s⁻¹ * (s * b * s⁻¹) = a * b := by
      calc s * a * s⁻¹ * (s * b * s⁻¹) = s * (a * b) * s⁻¹ := by group
        _ = a * b := by rw [hc]; group
    calc a⁻¹ * (s * a * s⁻¹) = a⁻¹ * (s * a * s⁻¹ * (s * b * s⁻¹)) * (s * b * s⁻¹)⁻¹ := by group
      _ = a⁻¹ * (a * b) * (s * b * s⁻¹)⁻¹ := by rw [e]
      _ = b * (s * b * s⁻¹)⁻¹ := by group
  have h1 : a⁻¹ * (s * a * s⁻¹) ∈ W₁ ⊓ W₂ := ⟨hu, huv ▸ hv⟩
  rw [hsum, Subgroup.mem_bot] at h1
  have h2 : s * a * s⁻¹ = a := by
    have := mul_eq_one_iff_eq_inv.mp h1
    calc s * a * s⁻¹ = a * (a⁻¹ * (s * a * s⁻¹)) := by group
      _ = a := by rw [h1, mul_one]
  calc s * a = (s * a * s⁻¹) * s := by group
    _ = a * s := by rw [h2]

theorem T_le_normalizer_VZ (h : Hyp5_1_14 G T M L V H B D n) :
    T ≤ Subgroup.normalizer (conjClosure (quasithinOmegaOneCenter T) L : Set G) := by
  intro t ht
  have hTL : t ∈ Subgroup.normalizer (L : Set G) :=
    h.hyp.toHyp5_0_1.normal (h.hyp.toHyp5_0_1.T_le ht)
  refine normalizer_conjClosure_of_centralizes _ hTL (fun k hk => ?_)
  have hkC := Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_inf T hk).2 t ht
  rw [hkC, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_natural_z (s : Setup521 G T M L V H B D D₃ Z₁ n) (h5114 : Stmt5_1_14_first)
    (hF : L2TorusFact) (h522 : Stmt5_1_22) {z : G} (hz : z ∈ Z₁) (hz1 : z ≠ 1) :
    (n = 2 ∨ n = 4) ∧ ∃ N : Subgroup G, z ∈ N ∧ N ≤ conjClosure (quasithinOmegaOneCenter T) L ∧
      L ≤ Subgroup.normalizer (N : Set G) ∧
      T ≤ Subgroup.normalizer (N : Set G) ∧
      (∀ X : Subgroup G, X ≤ N → L ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = N) ∧
      ∃ D : NatL2Data L N n, D.SylowAdapted (T ⊓ L) := by
  have hh := s.hyp.hyp.toHyp5_0_1
  set VZ := conjClosure (quasithinOmegaOneCenter T) L with hVZdef
  set VL : Subgroup G := ⁅VZ, L⁆ with hVLdef
  have hnotZ : ¬ Concl5_1_14_four T L VZ B D n := by
    rintro ⟨-, -, hDB⟩
    apply s.not_le
    have h1 : D₃ ≤ B := hDB ▸ s.le_D
    exact h1.trans ((s.hyp.notation59.1.1.trans inf_le_right).trans (le_normalizer_oTwoUpper H))
  have hn := (h522 G T M L VZ H B D D₃ Z₁ n s.hyp.hyp s.hyp.notation59
    (isCh5Module_VZ s.hyp h5114) s.hyp.l34 hnotZ s.le_D s.card_D₃ s.z1).2.1
  refine ⟨hn.1, ?_⟩
  have hS : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf le_sup_right) le_sup_left hh.sup_le_normalizer
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hh.T_le.trans hh.normal
  have hVZn : ∀ ℓ ∈ L, ∀ x ∈ VZ, ℓ * x * ℓ⁻¹ ∈ VZ := fun ℓ hℓ x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ L hℓ) x).mp hx
  have hzVL : z ∈ VL := V₂_le_commVL s h5114 hF (le_conjClosure Z₁ D₃ hz)
  have hTz : ∀ t ∈ T, t * z * t⁻¹ = z := fun t ht => by
    have hkC := Subgroup.mem_centralizer_iff.mp
      (quasithinOmegaOneCenter_le_inf T (s.Z₁_le_Z hz)).2 t ht
    rw [hkC, mul_assoc, mul_inv_cancel, mul_one]
  have hTVL : T ≤ Subgroup.normalizer (VL : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hclos : ∀ g ∈ T, ∀ y ∈ VL, g * y * g⁻¹ ∈ VL := fun g hg y hy =>
      conj_mem_commVL' (T_le_normalizer_VZ s.hyp hg) (hTL hg) hy
    constructor
    · exact hclos t ht x
    · intro hx
      have h1 := hclos t⁻¹ (T.inv_mem ht) _ hx
      have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
      rwa [e] at h1
  have hLVL : L ≤ Subgroup.normalizer (VL : Set G) := by
    intro ℓ hℓ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hclos : ∀ g ∈ L, ∀ y ∈ VL, g * y * g⁻¹ ∈ VL := fun g hg y hy =>
      conj_mem_commVL' (le_normalizer_conjClosure _ L hg) (Subgroup.le_normalizer hg) hy
    constructor
    · exact hclos ℓ hℓ x
    · intro hx
      have h1 := hclos ℓ⁻¹ (L.inv_mem hℓ) _ hx
      have e : ℓ⁻¹ * (ℓ * x * ℓ⁻¹) * ℓ⁻¹⁻¹ = x := by group
      rwa [e] at h1
  have hVZab : ∀ a ∈ VZ, ∀ b ∈ VZ, a * b = b * a := fun a ha b hb =>
    mul_comm_of_isMulCommutative (isElemAbelian_VZ s.hyp).1 ha hb
  have hVLVZ : VL ≤ VZ := commVL_le_VZ hVZn
  rcases hn.2 with hA | hB
  ·
    obtain ⟨D, hD⟩ := hA.exists_sylowAdapted hS
    exact ⟨VL, hzVL, hVLVZ, hLVL, hTVL, fun X hX hLX => hA.irreducible X (hX.trans le_rfl) hLX, D, hD⟩
  ·
    obtain ⟨W₁, W₂, hW₁L, hW₂L, hsum, hsup, hW₁n, hW₂n⟩ := hB
    have hW₁VL : W₁ ≤ VL := le_sup_left.trans hsup.le
    have hW₂VL : W₂ ≤ VL := le_sup_right.trans hsup.le
    have hW₁VZ : W₁ ≤ VZ := hW₁VL.trans hVLVZ
    have hW₂VZ : W₂ ≤ VZ := hW₂VL.trans hVLVZ
    have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
      hVZab a (hW₁VZ ha) b (hW₂VZ hb)
    have hzsup : z ∈ W₁ ⊔ W₂ := hsup.ge hzVL
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_comm_decomp hcomm hzsup
    have hS₁ : ∀ g ∈ T ⊓ L, ∀ x ∈ W₁, g * x * g⁻¹ ∈ W₁ := fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (hW₁L hg.2) x).mp hx
    have hS₂ : ∀ g ∈ T ⊓ L, ∀ x ∈ W₂, g * x * g⁻¹ ∈ W₂ := fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (hW₂L hg.2) x).mp hx
    have hzC : z ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hgz := hTz g hg.1
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [hgz]
    have haC : a ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
      mem_centralizer_of_mul hS₁ hS₂ hsum ha hb (by rw [hab]; exact hzC)
    have hbC : b ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
      mem_centralizer_of_mul hS₂ hS₁ (by rw [inf_comm]; exact hsum) hb ha
        (by rw [(hcomm a ha b hb).symm.trans hab]; exact hzC)
    by_cases ha1 : a = 1
    ·
      have hzW₂ : z ∈ W₂ := by
        rw [← hab, ha1, one_mul]
        exact hb
      obtain ⟨D, hD⟩ := hW₂n.exists_sylowAdapted hS
      exact ⟨W₂, hzW₂, hW₂VL.trans hVLVZ, hW₂L, fun t ht => normalizes_of_irreducible hzW₂ hz1 hW₂L
        (fun X hX hLX => hW₂n.irreducible X hX hLX) (hTL ht) (hTz t ht),
        fun X hX hLX => hW₂n.irreducible X hX hLX, D, hD⟩
    by_cases hb1 : b = 1
    ·
      have hzW₁ : z ∈ W₁ := by
        rw [← hab, hb1, mul_one]
        exact ha
      obtain ⟨D, hD⟩ := hW₁n.exists_sylowAdapted hS
      exact ⟨W₁, hzW₁, hW₁VL.trans hVLVZ, hW₁L, fun t ht => normalizes_of_irreducible hzW₁ hz1 hW₁L
        (fun X hX hLX => hW₁n.irreducible X hX hLX) (hTL ht) (hTz t ht),
        fun X hX hLX => hW₁n.irreducible X hX hLX, D, hD⟩
    obtain ⟨D₁, hD₁⟩ := hW₁n.exists_sylowAdapted hS
    obtain ⟨D₂, hD₂⟩ := hW₂n.exists_sylowAdapted hS
    obtain ⟨Γ, hzΓ, hΓsub, hΓL, hΓirr, D, hD⟩ := exists_diag D₁ D₂ inf_le_right hD₁ hD₂ hsum hcomm
      (ker_eq_of_natural s.hyp h5114 hW₁n hW₂n hW₁VZ hW₂VZ)
      (fun X hX hLX => hW₁n.irreducible X hX hLX) ha hb ha1 hb1 haC hbC
    rw [hab] at hzΓ
    exact ⟨Γ, hzΓ, hΓsub.trans (hsup.le.trans hVLVZ), hΓL, fun t ht => normalizes_of_irreducible hzΓ hz1 hΓL hΓirr (hTL ht)
      (hTz t ht), hΓirr, D, hD⟩

end CFSG.Quasithin.H13
