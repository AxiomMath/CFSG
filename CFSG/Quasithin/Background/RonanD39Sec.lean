module

public import CFSG.Quasithin.EmptyFaithful.S153ZE

public section

namespace CFSG.Quasithin.RonanD39

open scoped Pointwise
open CFSG.Quasithin.Z391

section Count

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

@[expose] def fixMod (B : Subgroup Γ) (P : Subgroup Q) : Subgroup Q where
  carrier := {x | ∀ b ∈ B, b • x * x⁻¹ ∈ P}
  one_mem' := fun b _ => by simp
  mul_mem' := by
    intro x y hx hy b hb
    have e : b • (x * y) * (x * y)⁻¹ = b • x * x⁻¹ * (b • y * y⁻¹) := by
      rw [smul_mul', mul_inv]
      ac_rfl
    rw [e]
    exact P.mul_mem (hx b hb) (hy b hb)
  inv_mem' := by
    intro x hx b hb
    have e : b • x⁻¹ * x⁻¹⁻¹ = (b • x * x⁻¹)⁻¹ := by
      rw [smul_inv', mul_inv]
    rw [e]
    exact P.inv_mem (hx b hb)

theorem mem_fixMod {B : Subgroup Γ} {P : Subgroup Q} {x : Q} :
    x ∈ fixMod B P ↔ ∀ b ∈ B, b • x * x⁻¹ ∈ P := Iff.rfl

theorem le_fixMod {B : Subgroup Γ} {P : Subgroup Q} (hP : XMod.IsInv ↥B P) : P ≤ fixMod B P :=
  fun x hx b hb => P.mul_mem (hP ⟨b, hb⟩ x hx) (P.inv_mem hx)

theorem fixMod_mono (B : Subgroup Γ) {P P' : Subgroup Q} (h : P ≤ P') : fixMod B P ≤ fixMod B P' :=
  fun _ hx b hb => h (hx b hb)

theorem fixMod_bot (B : Subgroup Γ) : fixMod B (⊥ : Subgroup Q) = XMod.fixed ↥B ⊤ := by
  ext x
  simp only [mem_fixMod, Subgroup.mem_bot, mul_inv_eq_one, XMod.mem_fixed, Subgroup.mem_top,
    true_and]
  exact ⟨fun h b => h b b.2, fun h b hb => h ⟨b, hb⟩⟩

@[expose] noncomputable def nS (B : Subgroup Γ) (P X : Subgroup Q) : ℕ :=
  rk ↥X - rk ↥(X ⊓ fixMod B P)

theorem nS_bot (B : Subgroup Γ) (X : Subgroup Q) : nS B ⊥ X = nB B X := by
  unfold nS nB
  rw [fixMod_bot]

theorem nS_add_le [Finite Q] {B : Subgroup Γ} {P X Y : Subgroup Q} (hPX : P ≤ X) (hXY : X ≤ Y)
    (hX : XMod.IsInv ↥B X) : nS B P X + nS B X Y ≤ nS B P Y := by
  unfold nS
  have h1 := rk_sup_add_rk_inf (Y ⊓ fixMod B P) X
  have h2 : (Y ⊓ fixMod B P) ⊔ X ≤ Y ⊓ fixMod B X :=
    sup_le (inf_le_inf_left _ (fixMod_mono B hPX)) (le_inf hXY (le_fixMod hX))
  have h3 : (Y ⊓ fixMod B P) ⊓ X = X ⊓ fixMod B P := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hXY h.1, h.2⟩, h.1⟩⟩
  rw [h3] at h1
  have h4 := rk_mono h2
  have h5 : rk ↥(X ⊓ fixMod B P) ≤ rk ↥X := rk_mono inf_le_left
  have h6 : rk ↥(Y ⊓ fixMod B X) ≤ rk ↥Y := rk_mono inf_le_left
  have h7 : rk ↥(Y ⊓ fixMod B P) ≤ rk ↥Y := rk_mono inf_le_left
  omega

theorem rk_map_add_rk_inf_ker {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (K : Subgroup G) (f : G →* H) : rk ↥(K.map f) + rk ↥(K ⊓ f.ker) = rk ↥K := by
  have h1 := B1More.card_map_mul_card_inf_ker K f
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h1]

theorem nB_map_quotMod [Finite Q] {H B : Subgroup Γ} (hBH : B ≤ H) {P : Subgroup Q}
    (hP : ∀ g : ↥H, ∀ x ∈ P, g • x ∈ P) {X : Subgroup Q} (hPX : P ≤ X) :
    nB (B.subgroupOf H) (X.map (QuotMod.mk P hP)) = nS B P X := by
  unfold nB nS
  set mk := QuotMod.mk P hP with hmk
  have hker : mk.ker = P := QuotMod.ker_mk P hP
  have hPB : XMod.IsInv ↥B P := fun b x hx => hP ⟨b, hBH b.2⟩ x hx
  have hPF : P ≤ X ⊓ fixMod B P := le_inf hPX (le_fixMod hPB)
  have hmap : X.map mk ⊓ XMod.fixed ↥(B.subgroupOf H) (⊤ : Subgroup (QuotMod P hP)) =
      (X ⊓ fixMod B P).map mk := by
    ext z
    simp only [Subgroup.mem_inf, Subgroup.mem_map, XMod.mem_fixed, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hfix⟩
      refine ⟨x, ⟨hx, fun b hb => ?_⟩, rfl⟩
      have h1 := hfix ⟨⟨b, hBH hb⟩, hb⟩
      change mk (b • x) = mk x at h1
      rw [← hker, MonoidHom.mem_ker, map_mul, h1, map_inv, mul_inv_cancel]
    · rintro ⟨x, ⟨hx, hxF⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, fun b => ?_⟩
      change mk (((b : ↥H) : Γ) • x) = mk x
      have h1 : ((b : ↥H) : Γ) • x * x⁻¹ ∈ mk.ker := by
        rw [hker]
        exact hxF _ b.2
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1
  rw [hmap]
  have h1 := rk_map_add_rk_inf_ker X mk
  have h2 := rk_map_add_rk_inf_ker (X ⊓ fixMod B P) mk
  rw [hker, inf_eq_right.2 hPX] at h1
  rw [hker, inf_eq_right.2 hPF] at h2
  have h3 : rk ↥(X ⊓ fixMod B P) ≤ rk ↥X := rk_mono inf_le_left
  omega

end Count

section Chain

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

inductive LChain (Λ : Subgroup Γ) (d : ℕ) : Subgroup Q → Subgroup Q → ℕ → Prop
  | refl (X : Subgroup Q) : LChain Λ d X X 0
  | snoc {X Y Z : Subgroup Q} {k : ℕ} : LChain Λ d X Y k → XMod.IsInv ↥Λ Y → XMod.IsInv ↥Λ Z →
      XMod.IsIrrSec ↥Λ Y Z → rk ↥Z = rk ↥Y + d → LChain Λ d X Z (k + 1)

variable {Λ : Subgroup Γ} {d : ℕ}

theorem LChain.trans {X Y Z : Subgroup Q} {k l : ℕ} (h₁ : LChain Λ d X Y k)
    (h₂ : LChain Λ d Y Z l) : LChain Λ d X Z (k + l) := by
  induction h₂ with
  | refl => simpa using h₁
  | snoc _ hY hZ hYZ hrk ih => exact LChain.snoc ih hY hZ hYZ hrk

theorem LChain.rk_eq {X Y : Subgroup Q} {k : ℕ} (h : LChain Λ d X Y k) :
    rk ↥Y = rk ↥X + k * d := by
  induction h with
  | refl => simp
  | snoc _ _ _ _ hrk ih => rw [hrk, ih]; ring

theorem LChain.le {X Y : Subgroup Q} {k : ℕ} (h : LChain Λ d X Y k) : X ≤ Y := by
  induction h with
  | refl => exact le_rfl
  | snoc _ _ _ hYZ _ ih => exact ih.trans hYZ.1.le

theorem LChain.exists_series {X Y : Subgroup Q} {k : ℕ} (h : LChain Λ d X Y k) :
    ∃ N : Fin (k + 1) → Subgroup Q, N 0 = X ∧ N (Fin.last k) = Y ∧
      ∀ i : Fin k, XMod.IsInv ↥Λ (N i.castSucc) ∧ XMod.IsInv ↥Λ (N i.succ) ∧
        XMod.IsIrrSec ↥Λ (N i.castSucc) (N i.succ) := by
  induction h with
  | refl => exact ⟨fun _ => X, rfl, rfl, fun i => i.elim0⟩
  | @snoc Y Z k _ hY hZ hYZ _ ih =>
    obtain ⟨N, h0, hl, hs⟩ := ih
    refine ⟨Fin.snoc N Z, ?_, ?_, ?_⟩
    · have e : (0 : Fin (k + 1 + 1)) = Fin.castSucc (0 : Fin (k + 1)) := rfl
      rw [e, Fin.snoc_castSucc, h0]
    · exact Fin.snoc_last _ _
    · intro i
      induction i using Fin.lastCases with
      | last =>
        rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hl]
        exact ⟨hY, hZ, hYZ⟩
      | cast j =>
        rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
        exact hs j

theorem isIrrSec_sup_of_disjoint [Finite Q] {Y X : Subgroup Q} (hY : XMod.IsInv ↥Λ Y)
    (hX : XMod.IsIrr ↥Λ X) (hYX : Y ⊓ X = ⊥) :
    XMod.IsInv ↥Λ (Y ⊔ X) ∧ XMod.IsIrrSec ↥Λ Y (Y ⊔ X) ∧ rk ↥(Y ⊔ X) = rk ↥Y + rk ↥X := by
  refine ⟨hY.sup hX.1, ⟨?_, fun J hJ hYJ hJ' => ?_⟩, ?_⟩
  · refine lt_of_le_of_ne le_sup_left fun h => ?_
    have hXY : X ≤ Y := h ▸ le_sup_right
    have : X = ⊥ := by rw [← hYX]; exact (inf_eq_right.2 hXY).symm
    exact hX.2.1.ne' this
  · rcases hX.2.2 (J ⊓ X) (hJ.inf hX.1) bot_le inf_le_right with h | h
    · left
      refine le_antisymm (fun j hj => ?_) hYJ
      obtain ⟨y, hy, x, hx, rfl⟩ := Subgroup.mem_sup.1 (hJ' hj)
      have hxJ : x ∈ J := by
        have := J.mul_mem (J.inv_mem (hYJ hy)) hj
        rwa [inv_mul_cancel_left] at this
      have hx1 : x = 1 := by
        have : x ∈ J ⊓ X := ⟨hxJ, hx⟩
        rwa [h, Subgroup.mem_bot] at this
      rw [hx1, mul_one]
      exact hy
    · right
      exact le_antisymm hJ' (sup_le hYJ (h ▸ inf_le_left))
  · have := rk_sup_add_rk_inf Y X
    rw [hYX, rk_bot] at this
    omega

theorem isInv_finset_sup (s : Finset (Subgroup Q)) (h : ∀ X ∈ s, XMod.IsInv ↥Λ X) :
    XMod.IsInv ↥Λ (s.sup id) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact XMod.isInv_bot
  | insert X s _ ih =>
    rw [Finset.sup_insert]
    exact (h X (by simp)).sup (ih fun Y hY => h Y (by simp [hY]))

theorem LChain.of_sSupIndep [Finite Q] (s : Finset (Subgroup Q))
    (hirr : ∀ X ∈ s, XMod.IsIrr ↥Λ X ∧ rk ↥X = d) (hind : sSupIndep (s : Set (Subgroup Q))) :
    LChain Λ d ⊥ (s.sup id) s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => exact LChain.refl ⊥
  | insert X s hXs ih =>
    have hind' : sSupIndep (s : Set (Subgroup Q)) :=
      hind.mono (by simp [Set.subset_insert])
    have hirr' : ∀ Y ∈ s, XMod.IsIrr ↥Λ Y ∧ rk ↥Y = d := fun Y hY => hirr Y (by simp [hY])
    have h1 := ih hirr' hind'
    obtain ⟨hXirr, hXd⟩ := hirr X (by simp)
    have hdisj : Disjoint X (sSup (s : Set (Subgroup Q))) :=
      hind.disjoint_sSup (by simp) (by simp [Set.subset_insert]) (by simpa using hXs)
    rw [← Finset.sup_id_eq_sSup] at hdisj
    have hinv : XMod.IsInv ↥Λ (s.sup id) := isInv_finset_sup s fun Y hY => (hirr' Y hY).1.1
    obtain ⟨h2, h3, h4⟩ := isIrrSec_sup_of_disjoint hinv hXirr
      (by rw [inf_comm]; exact disjoint_iff.1 hdisj)
    rw [Finset.sup_insert, Finset.card_insert_of_notMem hXs]
    have e : id X ⊔ s.sup id = s.sup id ⊔ X := sup_comm _ _
    rw [e]
    exact LChain.snoc h1 hinv h2 h3 (by rw [h4, hXd])

theorem isInv_comap_quotMod {H Λ : Subgroup Γ} (hΛH : Λ ≤ H) {P : Subgroup Q}
    (hP : ∀ g : ↥H, ∀ x ∈ P, g • x ∈ P) {J : Subgroup (QuotMod P hP)}
    (hJ : XMod.IsInv ↥(Λ.subgroupOf H) J) : XMod.IsInv ↥Λ (J.comap (QuotMod.mk P hP)) := by
  intro l x hx
  have := hJ ⟨⟨(l : Γ), hΛH l.2⟩, l.2⟩ _ hx
  exact this

theorem isInv_map_quotMod {H Λ : Subgroup Γ} {P : Subgroup Q}
    (hP : ∀ g : ↥H, ∀ x ∈ P, g • x ∈ P) {J : Subgroup Q} (hJ : XMod.IsInv ↥Λ J) :
    XMod.IsInv ↥(Λ.subgroupOf H) (J.map (QuotMod.mk P hP)) := by
  rintro l _ ⟨x, hx, rfl⟩
  exact ⟨((l : ↥H) : Γ) • x, hJ ⟨((l : ↥H) : Γ), l.2⟩ x hx, rfl⟩

theorem rk_comap_quotMod [Finite Q] {H : Subgroup Γ} {P : Subgroup Q}
    (hP : ∀ g : ↥H, ∀ x ∈ P, g • x ∈ P) (J : Subgroup (QuotMod P hP)) :
    rk ↥(J.comap (QuotMod.mk P hP)) = rk ↥J + rk ↥P := by
  have h1 := rk_map_add_rk_inf_ker (J.comap (QuotMod.mk P hP)) (QuotMod.mk P hP)
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotMod.mk_surjective P hP), QuotMod.ker_mk,
    inf_eq_right.2 (fun x hx => by
      change QuotMod.mk P hP x ∈ J
      rw [← QuotMod.ker_mk P hP] at hx
      rw [MonoidHom.mem_ker.1 hx]
      exact J.one_mem)] at h1
  omega

theorem isIrrSec_comap_quotMod {H Λ : Subgroup Γ} (hΛH : Λ ≤ H) {P : Subgroup Q}
    (hP : ∀ g : ↥H, ∀ x ∈ P, g • x ∈ P) {Y Z : Subgroup (QuotMod P hP)}
    (h : XMod.IsIrrSec ↥(Λ.subgroupOf H) Y Z) :
    XMod.IsIrrSec ↥Λ (Y.comap (QuotMod.mk P hP)) (Z.comap (QuotMod.mk P hP)) := by
  have hsurj := QuotMod.mk_surjective P hP
  refine ⟨lt_of_le_of_ne (Subgroup.comap_mono h.1.le) fun he => h.1.ne ?_, fun J hJ hYJ hJZ => ?_⟩
  · have := congrArg (Subgroup.map (QuotMod.mk P hP)) he
    rwa [Subgroup.map_comap_eq_self_of_surjective hsurj,
      Subgroup.map_comap_eq_self_of_surjective hsurj] at this
  · have hJ' : XMod.IsInv ↥(Λ.subgroupOf H) (J.map (QuotMod.mk P hP)) := isInv_map_quotMod hP hJ
    have h1 : Y ≤ J.map (QuotMod.mk P hP) := by
      have := Subgroup.map_mono (f := QuotMod.mk P hP) hYJ
      rwa [Subgroup.map_comap_eq_self_of_surjective hsurj] at this
    have h2 : J.map (QuotMod.mk P hP) ≤ Z := by
      have := Subgroup.map_mono (f := QuotMod.mk P hP) hJZ
      rwa [Subgroup.map_comap_eq_self_of_surjective hsurj] at this
    have hPJ : P ≤ J := by
      refine le_trans ?_ hYJ
      intro x hx
      change QuotMod.mk P hP x ∈ Y
      rw [← QuotMod.ker_mk P hP] at hx
      rw [MonoidHom.mem_ker.1 hx]
      exact Y.one_mem
    have hJeq : (J.map (QuotMod.mk P hP)).comap (QuotMod.mk P hP) = J := by
      rw [Subgroup.comap_map_eq, QuotMod.ker_mk, sup_eq_left.2 hPJ]
    rcases h.2 _ hJ' h1 h2 with h3 | h3
    · left
      rw [← hJeq, h3]
    · right
      rw [← hJeq, h3]

theorem LChain.comap_quotMod [Finite Q] {H : Subgroup Γ} (hΛH : Λ ≤ H) {P : Subgroup Q}
    (hP : ∀ g : ↥H, ∀ x ∈ P, g • x ∈ P) {X Y : Subgroup (QuotMod P hP)} {k : ℕ}
    (h : LChain (Λ.subgroupOf H) d X Y k) :
    LChain Λ d (X.comap (QuotMod.mk P hP)) (Y.comap (QuotMod.mk P hP)) k := by
  induction h with
  | refl => exact LChain.refl _
  | snoc _ hY hZ hYZ hrk ih =>
    refine LChain.snoc ih (isInv_comap_quotMod hΛH hP hY) (isInv_comap_quotMod hΛH hP hZ)
      (isIrrSec_comap_quotMod hΛH hP hYZ) ?_
    rw [rk_comap_quotMod, rk_comap_quotMod, hrk]
    ring

end Chain

section Hom

variable {G : Type*} [Group G] {Q₁ Q₂ : Type*} [CommGroup Q₁] [CommGroup Q₂]
  [MulDistribMulAction G Q₁] [MulDistribMulAction G Q₂]

@[expose] def EqvOn (S : Subgroup G) (Y : Subgroup Q₁) (φ : ↥Y →* Q₂) : Prop :=
  ∀ g ∈ S, ∀ (y : ↥Y) (h : g • (y : Q₁) ∈ Y), φ ⟨g • (y : Q₁), h⟩ = g • φ y

theorem injective_of_eqvOn {S : Subgroup G} {Y : Subgroup Q₁} (hY : XMod.IsIrr ↥S Y)
    {φ : ↥Y →* Q₂} (hφ : EqvOn S Y φ) (hne : φ ≠ 1) : Function.Injective φ := by
  set K : Subgroup Q₁ := (φ.ker).map Y.subtype with hK
  have hKS : XMod.IsInv ↥S K := by
    rintro l _ ⟨k, hk, rfl⟩
    have hlk : (l : G) • (k : Q₁) ∈ Y := hY.1 l k k.2
    refine ⟨⟨(l : G) • (k : Q₁), hlk⟩, ?_, rfl⟩
    have hk' : φ k = 1 := hk
    show φ ⟨(l : G) • (k : Q₁), hlk⟩ = 1
    rw [hφ l l.2 k hlk, hk', smul_one]
  rcases hY.2.2 K hKS bot_le (Subgroup.map_subtype_le _) with h | h
  · rw [← MonoidHom.ker_eq_bot_iff]
    refine (Subgroup.eq_bot_iff_forall _).2 fun k hk => ?_
    have hk' : (k : Q₁) ∈ K := ⟨k, hk, rfl⟩
    rw [h, Subgroup.mem_bot] at hk'
    exact Subtype.ext hk'
  · exfalso
    apply hne
    refine MonoidHom.ext fun v => ?_
    have hv : (v : Q₁) ∈ K := by rw [h]; exact v.2
    obtain ⟨v', hv', hvv'⟩ := hv
    have : v' = v := Subtype.ext hvv'
    rw [← this]
    exact hv'

theorem isIrr_range_of_eqvOn {S : Subgroup G} {Y : Subgroup Q₁} (hY : XMod.IsIrr ↥S Y)
    {φ : ↥Y →* Q₂} (hφ : EqvOn S Y φ) (hinj : Function.Injective φ) : XMod.IsIrr ↥S φ.range := by
  refine ⟨?_, ?_, ?_⟩
  · rintro l _ ⟨y, rfl⟩
    have hly : (l : G) • (y : Q₁) ∈ Y := hY.1 l y y.2
    exact ⟨⟨(l : G) • (y : Q₁), hly⟩, hφ l l.2 y hly⟩
  · rw [bot_lt_iff_ne_bot]
    intro h0
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hY.2.1.ne' ((Subgroup.eq_bot_iff_forall _).2 hcon)
    have h1 : φ ⟨y, hy⟩ ∈ φ.range := ⟨⟨y, hy⟩, rfl⟩
    rw [h0, Subgroup.mem_bot] at h1
    have h2 : (⟨y, hy⟩ : ↥Y) = 1 := hinj (h1.trans (map_one φ).symm)
    exact hy1 (congrArg Subtype.val h2)
  · intro J hJ _ hJr
    set K : Subgroup Q₁ := (J.comap φ).map Y.subtype with hK
    have hKS : XMod.IsInv ↥S K := by
      rintro l _ ⟨k, hk, rfl⟩
      have hlk : (l : G) • (k : Q₁) ∈ Y := hY.1 l k k.2
      refine ⟨⟨(l : G) • (k : Q₁), hlk⟩, ?_, rfl⟩
      show φ ⟨(l : G) • (k : Q₁), hlk⟩ ∈ J
      rw [hφ l l.2 k hlk]
      exact hJ l _ hk
    rcases hY.2.2 K hKS bot_le (Subgroup.map_subtype_le _) with h | h
    · left
      refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
      obtain ⟨y, rfl⟩ := hJr hz
      have hy : (y : Q₁) ∈ K := ⟨y, hz, rfl⟩
      rw [h, Subgroup.mem_bot] at hy
      have : y = 1 := Subtype.ext hy
      rw [this, map_one]
    · right
      refine le_antisymm hJr ?_
      rintro _ ⟨y, rfl⟩
      have hy : (y : Q₁) ∈ K := by rw [h]; exact y.2
      obtain ⟨y', hy', hyy'⟩ := hy
      have : y' = y := Subtype.ext hyy'
      rw [← this]
      exact hy'

theorem iso_range_of_eqvOn {S : Subgroup G} {Y : Subgroup Q₁} (hY : XMod.IsInv ↥S Y)
    {φ₁ φ₂ : ↥Y →* Q₂} (hφ₁ : EqvOn S Y φ₁) (hφ₂ : EqvOn S Y φ₂)
    (h₁ : Function.Injective φ₁) (h₂ : Function.Injective φ₂) :
    XMod.Iso ↥S φ₁.range φ₂.range := by
  refine ⟨(MonoidHom.ofInjective h₁).symm.trans (MonoidHom.ofInjective h₂), fun a l l' hll' => ?_⟩
  obtain ⟨y, hy⟩ := l.2
  obtain ⟨y', hy'⟩ := l'.2
  have hl : l = MonoidHom.ofInjective h₁ y := Subtype.ext hy.symm
  have hl' : l' = MonoidHom.ofInjective h₁ y' := Subtype.ext hy'.symm
  have hay : (a : G) • (y : Q₁) ∈ Y := hY a y y.2
  have hyy' : y' = ⟨(a : G) • (y : Q₁), hay⟩ := by
    apply h₁
    rw [hφ₁ a a.2 y hay, hy, hy']
    exact hll'.symm
  rw [hl, hl']
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MonoidHom.ofInjective_apply]
  rw [hyy', hφ₂ a a.2 y hay]
  rfl

theorem nB_range_of_eqvOn [Finite Q₁] [Finite Q₂] {B : Subgroup G} {Y : Subgroup Q₁}
    (hY : XMod.IsInv ↥B Y) {φ : ↥Y →* Q₂} (hφ : EqvOn B Y φ) (hinj : Function.Injective φ) :
    nB B φ.range = nB B Y := by
  unfold nB
  have hrk1 : rk ↥φ.range = rk ↥Y := by
    unfold rk
    exact congrArg (padicValNat 2) (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm)
  have hmap : φ.range ⊓ XMod.fixed ↥B (⊤ : Subgroup Q₂) =
      ((Y ⊓ XMod.fixed ↥B (⊤ : Subgroup Q₁)).subgroupOf Y).map φ := by
    ext z
    constructor
    · rintro ⟨⟨y, rfl⟩, hz⟩
      refine ⟨y, ?_, rfl⟩
      refine ⟨y.2, XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩⟩
      have hby : (b : G) • (y : Q₁) ∈ Y := hY b y y.2
      have h1 := (XMod.mem_fixed.1 hz).2 b
      change (b : G) • φ y = φ y at h1
      rw [← hφ b b.2 y hby] at h1
      exact congrArg Subtype.val (hinj h1)
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, rfl⟩, XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩⟩
      have hby : (b : G) • (y : Q₁) ∈ Y := hY b y y.2
      have h1 := (XMod.mem_fixed.1 hy.2).2 b
      change (b : G) • (y : Q₁) = y at h1
      change (b : G) • φ y = φ y
      rw [← hφ b b.2 y hby]
      congr 1
      exact Subtype.ext h1
  have hrk2 : rk ↥(φ.range ⊓ XMod.fixed ↥B (⊤ : Subgroup Q₂)) =
      rk ↥(Y ⊓ XMod.fixed ↥B (⊤ : Subgroup Q₁)) := by
    rw [hmap]
    unfold rk
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ φ hinj).toEquiv.symm]
    exact congrArg _ (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv)
  rw [hrk1, hrk2]

theorem map_smul_of_equivariant (θ : Q₁ →* Q₂) (hθ : ∀ (g : G) (x : Q₁), θ (g • x) = g • θ x)
    (g : G) (L : Subgroup Q₁) : (g • L).map θ = g • (L.map θ) := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨θ x, ⟨x, hx, rfl⟩, (hθ g x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨g • x, ⟨x, hx, rfl⟩, hθ g x⟩

theorem iso_of_iso_map {S : Subgroup G} (θ : Q₁ →* Q₂)
    (hθ : ∀ (g : G) (x : Q₁), θ (g • x) = g • θ x) {L₁ L₂ : Subgroup Q₁}
    (hL₂ : XMod.IsInv ↥S L₂) (h₁ : ∀ x ∈ L₁, θ x = 1 → x = 1) (h₂ : ∀ x ∈ L₂, θ x = 1 → x = 1)
    (h : XMod.Iso ↥S (L₁.map θ) (L₂.map θ)) : XMod.Iso ↥S L₁ L₂ := by
  obtain ⟨e, he⟩ := h
  have hinj : ∀ {L : Subgroup Q₁}, (∀ x ∈ L, θ x = 1 → x = 1) →
      Function.Injective (θ.subgroupMap L) := by
    intro L hL x y hxy
    have h1 : θ (x : Q₁) = θ (y : Q₁) := congrArg Subtype.val hxy
    have h2 : (x : Q₁) * (y : Q₁)⁻¹ = 1 :=
      hL _ (L.mul_mem x.2 (L.inv_mem y.2)) (by rw [map_mul, map_inv, h1, mul_inv_cancel])
    exact Subtype.ext (mul_inv_eq_one.1 h2)
  set θ₁ : ↥L₁ ≃* ↥(L₁.map θ) :=
    MulEquiv.ofBijective (θ.subgroupMap L₁) ⟨hinj h₁, θ.subgroupMap_surjective L₁⟩
  set θ₂ : ↥L₂ ≃* ↥(L₂.map θ) :=
    MulEquiv.ofBijective (θ.subgroupMap L₂) ⟨hinj h₂, θ.subgroupMap_surjective L₂⟩
  refine ⟨θ₁.trans (e.trans θ₂.symm), fun a l l' hll' => ?_⟩
  have hm : (a : G) • ((θ₁ l : ↥(L₁.map θ)) : Q₂) = ((θ₁ l' : ↥(L₁.map θ)) : Q₂) := by
    change (a : G) • θ (l : Q₁) = θ (l' : Q₁)
    rw [← hθ, ← hll']
    rfl
  have h1 := he a _ _ hm
  set x := θ₂.symm (e (θ₁ l)) with hx
  set x' := θ₂.symm (e (θ₁ l')) with hx'
  have hθx : θ (x : Q₁) = ((e (θ₁ l) : ↥(L₂.map θ)) : Q₂) := by
    have : θ₂ x = e (θ₁ l) := by rw [hx, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val this
  have hθx' : θ (x' : Q₁) = ((e (θ₁ l') : ↥(L₂.map θ)) : Q₂) := by
    have : θ₂ x' = e (θ₁ l') := by rw [hx', MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val this
  change (a : G) • (x : Q₁) = (x' : Q₁)
  have hax : (a : G) • (x : Q₁) ∈ L₂ := hL₂ a x x.2
  have h3 : θ ((a : G) • (x : Q₁) * (x' : Q₁)⁻¹) = 1 := by
    rw [map_mul, map_inv, hθ, hθx, hθx']
    change a • ((e (θ₁ l) : ↥(L₂.map θ)) : Q₂) * _ = 1
    rw [h1, mul_inv_cancel]
  exact mul_inv_eq_one.1 (h₂ _ (L₂.mul_mem hax (L₂.inv_mem x'.2)) h3)

end Hom

section SubgroupOf

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem isInv_subgroupOf_iff {Λ H : Subgroup Γ} (hΛH : Λ ≤ H) {J : Subgroup Q} :
    XMod.IsInv ↥(Λ.subgroupOf H) J ↔ XMod.IsInv ↥Λ J :=
  ⟨fun hJ a x hx => hJ ⟨⟨(a : Γ), hΛH a.2⟩, a.2⟩ x hx,
    fun hJ b x hx => hJ ⟨((b : ↥H) : Γ), b.2⟩ x hx⟩

theorem isIrr_subgroupOf_iff {Λ H : Subgroup Γ} (hΛH : Λ ≤ H) {L : Subgroup Q} :
    XMod.IsIrr ↥(Λ.subgroupOf H) L ↔ XMod.IsIrr ↥Λ L := by
  constructor
  · intro h
    exact ⟨(isInv_subgroupOf_iff hΛH).1 h.1, h.2.1,
      fun J hJ h1 h2 => h.2.2 J ((isInv_subgroupOf_iff hΛH).2 hJ) h1 h2⟩
  · intro h
    exact ⟨(isInv_subgroupOf_iff hΛH).2 h.1, h.2.1,
      fun J hJ h1 h2 => h.2.2 J ((isInv_subgroupOf_iff hΛH).1 hJ) h1 h2⟩

theorem iso_subgroupOf_iff {Λ H : Subgroup Γ} (hΛH : Λ ≤ H) {L L' : Subgroup Q} :
    XMod.Iso ↥(Λ.subgroupOf H) L L' ↔ XMod.Iso ↥Λ L L' := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun a l l' h => he ⟨⟨(a : Γ), hΛH a.2⟩, a.2⟩ l l' h⟩
  · rintro ⟨e, he⟩
    exact ⟨e, fun b l l' h => he ⟨((b : ↥H) : Γ), b.2⟩ l l' h⟩

end SubgroupOf

end CFSG.Quasithin.RonanD39
