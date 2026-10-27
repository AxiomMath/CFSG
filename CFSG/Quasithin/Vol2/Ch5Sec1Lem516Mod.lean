module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34DiscNat
public import CFSG.Quasithin.Vol2.Ch12Sec4A5Sum
public import CFSG.Quasithin.H13.A7FiveFixed
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.Vol2.Ch5Modules

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G]

section Sum

variable {W₁ W₂ : Subgroup G}

theorem exists_mul_of_mem_sup (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a) {x : G}
    (hx : x ∈ W₁ ⊔ W₂) : ∃ a ∈ W₁, ∃ b ∈ W₂, a * b = x := by
  have hW₂N : W₂ ≤ Subgroup.normalizer (W₁ : Set G) := by
    refine le_trans (fun b hb => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcomm a ha b hb
  have hx' : x ∈ ((W₁ ⊔ W₂ : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left W₁ W₂ hW₂N] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem eq_of_mul_eq (hdisj : W₁ ⊓ W₂ = ⊥) {a a' b b' : G} (ha : a ∈ W₁) (ha' : a' ∈ W₁)
    (hb : b ∈ W₂) (hb' : b' ∈ W₂) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a ∈ W₁ ⊓ W₂ := by
    refine Subgroup.mem_inf.mpr ⟨W₁.mul_mem (W₁.inv_mem ha') ha, ?_⟩
    have e : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    rw [e]
    exact W₂.mul_mem hb' (W₂.inv_mem hb)
  rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at h1
  subst h1
  exact ⟨rfl, mul_left_cancel h⟩

theorem conj_eq_of_conj_mul_eq (hdisj : W₁ ⊓ W₂ = ⊥) {g : G}
    (hg₁ : g ∈ Subgroup.normalizer (W₁ : Set G)) (hg₂ : g ∈ Subgroup.normalizer (W₂ : Set G))
    {a b : G} (ha : a ∈ W₁) (hb : b ∈ W₂) (h : g * (a * b) * g⁻¹ = a * b) :
    g * a * g⁻¹ = a ∧ g * b * g⁻¹ = b := by
  have e : (g * a * g⁻¹) * (g * b * g⁻¹) = a * b := by
    rw [← h]
    group
  exact eq_of_mul_eq hdisj ((Subgroup.mem_normalizer_iff.mp hg₁ a).mp ha) ha
    ((Subgroup.mem_normalizer_iff.mp hg₂ b).mp hb) hb e

theorem commutator_eq_of_sum {X W : Subgroup G} (hXW : X ≤ Subgroup.normalizer (W : Set G))
    (hsup : W₁ ⊔ W₂ = W) (h₁ : ⁅W₁, X⁆ = W₁) (h₂ : ⁅W₂, X⁆ = W₂) : ⁅W, X⁆ = W := by
  apply le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hXW)
  conv_lhs => rw [← hsup]
  refine sup_le ?_ ?_
  · rw [← h₁]
    exact Subgroup.commutator_mono (le_sup_left.trans hsup.le) le_rfl
  · rw [← h₂]
    exact Subgroup.commutator_mono (le_sup_right.trans hsup.le) le_rfl

theorem card_sup_eq_mul (hdisj : W₁ ⊓ W₂ = ⊥) (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a) :
    Nat.card ↥(W₁ ⊔ W₂) = Nat.card W₁ * Nat.card W₂ := by
  have h := B2F.card_sup_mul_card_inf_of_commute hcomm
  rwa [hdisj, Subgroup.card_bot, mul_one] at h

end Sum

section NatSum

variable {L : Subgroup G} {n : ℕ}

theorem eq_of_le_of_inf_eq_bot {W₁ W₂ V : Subgroup G} (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a)
    (h₁ : W₁ ≤ V) (hV : V ≤ W₁ ⊔ W₂) (h₂ : V ⊓ W₂ = ⊥) : V = W₁ := by
  refine le_antisymm (fun x hx => ?_) h₁
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm (hV hx)
  have hbV : b ∈ V ⊓ W₂ := by
    refine Subgroup.mem_inf.mpr ⟨?_, hb⟩
    have := V.mul_mem (V.inv_mem (h₁ ha)) hx
    rwa [inv_mul_cancel_left] at this
  rw [h₂, Subgroup.mem_bot] at hbV
  rw [hbV, mul_one]
  exact ha

theorem eq_or_isNatModCh5_of_le_sum [Finite G] {R V : Subgroup G}
    (hsum : IsSumOfTwo L R (fun W => IsNatModCh5 L W n)) (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hVR : V ≤ R) (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV : V ≠ ⊥) :
    V = R ∨ IsNatModCh5 L V n := by
  obtain ⟨W₁, W₂, hL₁, hL₂, hdisj, hsup, hW₁, hW₂⟩ := hsum
  have hW₁R : W₁ ≤ R := le_sup_left.trans hsup.le
  have hW₂R : W₂ ≤ R := le_sup_right.trans hsup.le
  have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
    hRc a (hW₁R ha) b (hW₂R hb)
  have hcomm' : ∀ a ∈ W₂, ∀ b ∈ W₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hVs : V ≤ W₁ ⊔ W₂ := hVR.trans hsup.ge
  have hVs' : V ≤ W₂ ⊔ W₁ := hVs.trans (sup_comm W₁ W₂).le
  have hN₁ : L ≤ Subgroup.normalizer ((V ⊓ W₁ : Subgroup G) : Set G) := fun _ hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hLV hl, hL₁ hl⟩
  have hN₂ : L ≤ Subgroup.normalizer ((V ⊓ W₂ : Subgroup G) : Set G) := fun _ hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hLV hl, hL₂ hl⟩
  rcases hW₁.irreducible (V ⊓ W₁) inf_le_right hN₁ with h₁ | h₁
  · rcases hW₂.irreducible (V ⊓ W₂) inf_le_right hN₂ with h₂ | h₂
    ·
      right
      choose a ha b hb hab using fun v : ↥V => exists_mul_of_mem_sup hcomm (hVs v.2)
      have huniq : ∀ (v : ↥V) {a' b' : G}, a' ∈ W₁ → b' ∈ W₂ → a' * b' = v → b v = b' :=
        fun v a' b' ha' hb' h' => (eq_of_mul_eq hdisj (ha v) ha' (hb v) hb'
          ((hab v).trans h'.symm)).2
      let F : ↥V →* ↥W₂ :=
        { toFun := fun v => ⟨b v, hb v⟩
          map_one' := Subtype.ext (huniq 1 W₁.one_mem W₂.one_mem (by simp))
          map_mul' := fun v w => Subtype.ext (by
            refine huniq (v * w) (W₁.mul_mem (ha v) (ha w)) (W₂.mul_mem (hb v) (hb w)) ?_
            show a v * a w * (b v * b w) = (v : G) * w
            rw [← hab v, ← hab w]
            calc a v * a w * (b v * b w) = a v * (a w * b v) * b w := by group
              _ = a v * (b v * a w) * b w := by rw [hcomm' (b v) (hb v) (a w) (ha w)]
              _ = a v * b v * (a w * b w) := by group) }
      have hFv : ∀ v : ↥V, ((F v : ↥W₂) : G) = b v := fun _ => rfl
      have hFinj : Function.Injective F := by
        rw [injective_iff_map_eq_one]
        intro v hv
        have hb1 : b v = 1 := by
          have := congrArg Subtype.val hv
          simpa [hFv] using this
        have hvV : (v : G) ∈ V ⊓ W₁ := by
          refine Subgroup.mem_inf.mpr ⟨v.2, ?_⟩
          rw [← hab v, hb1, mul_one]
          exact ha v
        rw [h₁, Subgroup.mem_bot] at hvV
        exact Subtype.ext hvV
      have hFL : ∀ (l : G) (hl : l ∈ L) (v : ↥V),
          ((F (conjAct V ⟨l, hLV hl⟩ v) : ↥W₂) : G) = l * F v * l⁻¹ := by
        intro l hl v
        rw [hFv, hFv]
        refine huniq _ ((Subgroup.mem_normalizer_iff.mp (hL₁ hl) _).mp (ha v))
          ((Subgroup.mem_normalizer_iff.mp (hL₂ hl) _).mp (hb v)) ?_
        rw [conjAct_apply_coe, ← hab v]
        group
      set Im : Subgroup G := F.range.map W₂.subtype with hIm
      have hImW : Im ≤ W₂ := by
        rintro _ ⟨w, -, rfl⟩
        exact w.2
      have hLIm : L ≤ Subgroup.normalizer (Im : Set G) := by
        intro l hl
        have key : ∀ g ∈ L, ∀ x ∈ Im, g * x * g⁻¹ ∈ Im := by
          rintro g hg _ ⟨w, ⟨v, rfl⟩, rfl⟩
          refine ⟨F (conjAct V ⟨g, hLV hg⟩ v), ⟨_, rfl⟩, ?_⟩
          exact hFL g hg v
        rw [Subgroup.mem_normalizer_iff]
        intro x
        refine ⟨key l hl x, fun hx => ?_⟩
        have := key l⁻¹ (L.inv_mem hl) _ hx
        simpa [mul_assoc] using this
      have hImne : Im ≠ ⊥ := by
        obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV
        intro hb0
        apply hv1
        apply hFinj
        rw [map_one]
        apply Subtype.ext
        have : ((F v : ↥W₂) : G) ∈ Im := ⟨F v, ⟨v, rfl⟩, rfl⟩
        rw [hb0, Subgroup.mem_bot] at this
        exact this
      have hImeq : Im = W₂ := (hW₂.irreducible Im hImW hLIm).resolve_left hImne
      have hFsurj : Function.Surjective F := by
        intro w
        have hw : (w : G) ∈ Im := by
          rw [hImeq]
          exact w.2
        obtain ⟨w', ⟨v, rfl⟩, hw'⟩ := hw
        exact ⟨v, Subtype.ext hw'⟩
      let e : ↥V ≃* ↥W₂ := MulEquiv.ofBijective F ⟨hFinj, hFsurj⟩
      have hVc : IsMulCommutative ↥V :=
        ⟨⟨fun x y => Subtype.ext (hRc x (hVR x.2) y (hVR y.2))⟩⟩
      refine hW₂.of_mulEquiv hLV hVc e.symm fun l hl w => ?_
      obtain ⟨v, rfl⟩ := e.surjective w
      rw [MulEquiv.symm_apply_apply]
      have h1 : e (conjAct V ⟨l, hLV hl⟩ v) = conjAct W₂ ⟨l, hW₂.1 hl⟩ (e v) := by
        apply Subtype.ext
        rw [conjAct_apply_coe]
        exact hFL l hl v
      rw [← h1, MulEquiv.symm_apply_apply, conjAct_apply_coe]
    ·
      right
      have hle : W₂ ≤ V := h₂.ge.trans inf_le_left
      have heq := eq_of_le_of_inf_eq_bot hcomm' hle hVs' h₁
      rw [heq]
      exact hW₂
  · have hle₁ : W₁ ≤ V := h₁.ge.trans inf_le_left
    rcases hW₂.irreducible (V ⊓ W₂) inf_le_right hN₂ with h₂ | h₂
    · right
      have heq := eq_of_le_of_inf_eq_bot hcomm hle₁ hVs h₂
      rw [heq]
      exact hW₁
    · left
      have hle₂ : W₂ ≤ V := h₂.ge.trans inf_le_left
      exact le_antisymm hVR (hsup.ge.trans (sup_le hle₁ hle₂))

end NatSum

section A5

variable {L S : Subgroup G}

theorem card_ev5 : A5Mod.ev5.card = 16 := by
  decide

theorem IsA5ModuleUnder.card_eq (h : IsA5ModuleUnder L S) : Nat.card S = 16 := by
  obtain ⟨d⟩ := A5Mod.exists_data h
  let f : ↥S → ↥A5Mod.ev5 := fun w => ⟨d.β w, d.β_mem w w.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun w₁ w₂ h12 => Subtype.ext (d.β_inj w₁ w₁.2 w₂ w₂.2 (congrArg Subtype.val h12)),
      fun x => ?_⟩
    obtain ⟨w, hw, hwx⟩ := d.β_surj x x.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwx⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_finsetCard, card_ev5]

theorem IsA5ModuleUnder.eq_of_le (h : IsA5ModuleUnder L S) {U : Subgroup G} (hUS : U ≤ S)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) : U = S := by
  obtain ⟨d⟩ := A5Mod.exists_data h
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  refine le_antisymm hUS (d.le_of_mem (fun k hk x hx => ?_) (hUS u.2) u.2 ?_)
  · exact (Subgroup.mem_normalizer_iff.mp (hLU hk) x).mp hx
  · intro h1
    exact hu1 (Subtype.ext h1)

theorem IsA5ModuleUnder.inf_centralizer_eq_bot (h : IsA5ModuleUnder L S) :
    S ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  by_contra hne
  have hLC : L ≤ Subgroup.normalizer
      ((S ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    fun l hl => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h.1 hl, F7.normalizer_le_normalizer_centralizer L (Subgroup.le_normalizer hl)⟩
  have heq := h.eq_of_le inf_le_left hLC hne
  have hcomm := h.commutator_eq
  apply (show S ≠ ⊥ from by
    intro hb
    have := h.card_eq
    rw [hb, Subgroup.card_bot] at this
    omega)
  rw [← hcomm, Subgroup.commutator_eq_bot_iff_le_centralizer, ← heq]
  exact inf_le_right

end A5

section Comm

theorem commutator_eq_of_irreducible {L R V : Subgroup G}
    (hirr : ∀ U : Subgroup G, U ≤ ⁅R, L⁆ → L ≤ Subgroup.normalizer (U : Set G) → U ≠ ⊥ →
      U = ⁅R, L⁆)
    (hVR : V ≤ R) (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV : ⁅V, L⁆ ≠ ⊥) :
    ⁅V, L⁆ = ⁅R, L⁆ :=
  hirr _ (Subgroup.commutator_mono hVR le_rfl)
    (le_normalizer_commutator_of hLV Subgroup.le_normalizer) hV

theorem isBarS5_of_inf_centralizer_eq {L T V R : Subgroup G}
    (hV : L ⊔ T ≤ Subgroup.normalizer (V : Set G)) (hR : L ⊔ T ≤ Subgroup.normalizer (R : Set G))
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) =
      (L ⊔ T) ⊓ Subgroup.centralizer (R : Set G)) (h : IsBarS5 L T R) : IsBarS5 L T V := by
  obtain ⟨e⟩ := h
  have hker : (InternalSec.autOnHom hV).ker = (InternalSec.autOnHom hR).ker := by
    ext x
    rw [InternalSec.mem_ker_autOnHom, InternalSec.mem_ker_autOnHom]
    constructor
    · intro hx
      have h1 : (x : G) ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
        Subgroup.mem_inf.mpr ⟨x.2, hx⟩
      rw [hC] at h1
      exact (Subgroup.mem_inf.mp h1).2
    · intro hx
      have h1 : (x : G) ∈ (L ⊔ T) ⊓ Subgroup.centralizer (R : Set G) :=
        Subgroup.mem_inf.mpr ⟨x.2, hx⟩
      rw [← hC] at h1
      exact (Subgroup.mem_inf.mp h1).2
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective _
      (InternalSec.autOnHom_surjective hV)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (InternalSec.autOnHom_surjective hR)))).trans
    e⟩

variable [Finite G]

theorem borel_le_centralizer_of_split {T L R : Subgroup G} (hS : IsSylowTwoOf (T ⊓ L) L)
    (hsplit : IsCommCentralSplit L T R) (hA5 : IsA5ModuleUnder L ⁅R, L⁆)
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) :
    borelL T L ≤ Subgroup.centralizer
      ((R ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  obtain ⟨-, hsup⟩ := hsplit
  have hRL : ⁅R, L⁆ ≤ R := le_sup_left.trans hsup.le
  have hCR : R ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) ≤ R := inf_le_left
  have hcomm : ∀ a ∈ ⁅R, L⁆, ∀ b ∈ R ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G),
      a * b = b * a := fun a ha b hb => hRc a (hRL ha) b (hCR hb)
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro x hx'
  have hx : x ∈ R ∧ x ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mp hx'
  obtain ⟨y, hy, c, hc, rfl⟩ := exists_mul_of_mem_sup hcomm (hsup.ge hx.1)
  have hcL : ∀ l ∈ L ⊔ T, l * c = c * l :=
    fun l hl => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 l hl
  have hyS : ∀ s ∈ T ⊓ L, s * y * s⁻¹ = y := by
    intro s hs
    have h1 : s * (y * c) = y * c * s := Subgroup.mem_centralizer_iff.mp hx.2 s hs
    have h2 : s * c = c * s := hcL s (Subgroup.mem_sup_left (Subgroup.mem_inf.mp hs).2)
    have h3 : s * y = y * s := by
      have : s * y * c = y * s * c := by
        calc s * y * c = s * (y * c) := by group
          _ = y * c * s := h1
          _ = y * (c * s) := by group
          _ = y * (s * c) := by rw [h2]
          _ = y * s * c := by group
      exact mul_right_cancel this
    rw [h3, mul_inv_cancel_right]
  have hgL : g ∈ L := (Subgroup.mem_inf.mp hg).1
  have hgN : g ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := (Subgroup.mem_inf.mp hg).2
  have hgy := A7.IsA5ModuleUnder.conj_eq_of_fixed hA5 hS.2.1 hS.2.2 hgL hgN hy hyS
  have hgc : g * c = c * g := hcL g (Subgroup.mem_sup_left hgL)
  symm
  calc g * (y * c) = g * y * g⁻¹ * (g * c) := by group
    _ = y * (c * g) := by rw [hgy, hgc]
    _ = y * c * g := by group

end Comm

end CFSG.Quasithin.H13
