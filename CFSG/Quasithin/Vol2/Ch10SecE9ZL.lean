module

public import CFSG.Quasithin.Vol2.Ch10SecE9ZK
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.G64NatTop
public import CFSG.Quasithin.Background.FFC7D

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.EmptyFaithfulMultiple CFSG.Quasithin.B5

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem faithful_on_commV {G : Subgroup (MulAut V)} (hs : IsSimpleGroup ↥G)
    (hnab : ∃ a b : ↥G, a * b ≠ b * a) : ∀ g ∈ G, (∀ v ∈ commV G, g v = v) → g = 1 := by
  let N : Subgroup ↥G :=
    { carrier := {g | ∀ v ∈ commV G, (g : MulAut V) v = v}
      one_mem' := fun v _ => rfl
      mul_mem' := fun {a b} ha hb v hv => by
        show (a : MulAut V) ((b : MulAut V) v) = v
        rw [hb v hv, ha v hv]
      inv_mem' := fun {a} ha v hv => by
        show (a : MulAut V).symm v = v
        rw [MulEquiv.symm_apply_eq]
        exact (ha v hv).symm }
  have hNn : N.Normal := by
    constructor
    intro n hn k v hv
    have hkv : ((k⁻¹ : ↥G) : MulAut V) v ∈ commV G :=
      LRed4.commV_invariant_of_normalizer (Subgroup.le_normalizer (k⁻¹).2) hv
    show (k : MulAut V) ((n : MulAut V) (((k⁻¹ : ↥G) : MulAut V) v)) = v
    rw [hn _ hkv]
    simp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
  · intro g hg hgv
    have : (⟨g, hg⟩ : ↥G) ∈ N := hgv
    rw [hN, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hfix : ∀ g : ↥G, ∀ v ∈ commV G, (g : MulAut V) v = v := fun g =>
      (hN ▸ Subgroup.mem_top g : g ∈ N)
    have hδ : ∀ g h : ↥G, ∀ v : V, ((g * h : ↥G) : MulAut V) v * v⁻¹ =
        ((g : MulAut V) v * v⁻¹) * ((h : MulAut V) v * v⁻¹) := by
      intro g h v
      have hmem : (h : MulAut V) v * v⁻¹ ∈ commV G := Subgroup.subset_closure ⟨h, h.2, v, rfl⟩
      have h1 := hfix g _ hmem
      rw [map_mul, map_inv] at h1
      show (g : MulAut V) ((h : MulAut V) v) * v⁻¹ = _
      calc (g : MulAut V) ((h : MulAut V) v) * v⁻¹ =
            ((g : MulAut V) ((h : MulAut V) v) * ((g : MulAut V) v)⁻¹) *
              ((g : MulAut V) v * v⁻¹) := by rw [mul_assoc, inv_mul_cancel_left]
        _ = ((g : MulAut V) v * v⁻¹) * ((h : MulAut V) v * v⁻¹) := by rw [h1, mul_comm]
    apply hab
    ext v
    have e1 := hδ a b v
    have e2 := hδ b a v
    rw [mul_comm ((b : MulAut V) v * v⁻¹)] at e2
    have := e1.trans e2.symm
    exact mul_right_cancel this

theorem binaryNaturalSL_of_card_eight (hV2 : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    (hs : IsSimpleGroup ↥G) (hnab : ∃ a b : ↥G, a * b ≠ b * a) (hcard : Nat.card ↥G = 168)
    (h8 : Nat.card ↥(commV G) = 2 ^ 3) : BinaryNaturalSL G (commV G) ⊥ 3 1 := by
  have hfaith := faithful_on_commV hs hnab
  have hst : G ≤ stabSub (commV G) := FFC.B510.le_stabSub_commV fun g hg l hl =>
    G.mul_mem (G.mul_mem hg hl) (G.inv_mem hg)
  have hst0 : G ≤ stabSub (⊥ : Subgroup V) := fun g _ u => by
    simp only [Subgroup.mem_bot]
    exact ⟨fun h => g.injective (h.trans (map_one g).symm), fun h => by rw [h, map_one]⟩
  have hf : G ⊓ centSub (commV G) = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hg, hgc⟩
    exact Subgroup.mem_bot.mpr (hfaith g hg hgc)
  have hV2' : ∀ v : ↥(commV G), v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV2 v)
  obtain ⟨π, hπ⟩ := G64.realizesVia_top_of_card hV2' (n := 3) (by simpa using h8)
  have : Finite (MulAut ↥(commV G)) := Finite.of_injective _ DFunLike.coe_injective
  have hcardTop : Nat.card (MulAut ↥(commV G)) ≤ 168 := by
    have h1 := Nat.card_le_card_of_surjective π hπ.1
    rw [Subgroup.card_top, card_statedSL_three1527d, Nat.card_zmod] at h1
    norm_num at h1
    exact h1
  have hAut : Nat.card ↥(autSub G (commV G)) = 168 := by
    rw [FFC.card_autSub_eq hst fun g hg h => hfaith g hg h, hcard]
  have htop : autSub G (commV G) = ⊤ :=
    Subgroup.eq_top_of_le_card _ (by rw [hAut]; exact hcardTop)
  refine binaryNaturalSL_of_autSub hst hst0 bot_le hf
    ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num, ?_⟩
  rw [htop, Subgroup.bot_subgroupOf]
  exact ⟨π, hπ⟩

omit [Finite V] in
theorem modComm_top_eq (G : Subgroup (MulAut V)) : modComm G (⊤ : Subgroup V) = commV G := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, l, -, rfl⟩
    exact Subgroup.subset_closure ⟨g, g.2, l, rfl⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    exact Subgroup.subset_closure ⟨⟨x, hx⟩, v, trivial, rfl⟩

omit [Finite V] in
theorem commV_le_of_swap {G₁ G₂ : Subgroup (MulAut V)} {s : MulAut V}
    (hs : ∀ x ∈ G₁, s * x * s⁻¹ ∈ G₂) {u : V} (hu : u ∈ commV G₁) : s u ∈ commV G₂ := by
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    refine Subgroup.subset_closure ⟨s * x * s⁻¹, hs x hx, s v, ?_⟩
    simp [map_mul, map_inv]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

omit [Finite V] in
theorem mem_fixV_sup {G₁ G₂ : Subgroup (MulAut V)} {v : V} (h₁ : v ∈ fixV G₁)
    (h₂ : v ∈ fixV G₂) : v ∈ fixV (G₁ ⊔ G₂) :=
  CFSG.Quasithin.FixVLat.mem_fixV_sup h₁ h₂

theorem fixSec_top_le_of_case5 (hB48 : AsB4_8Three) (hV2 : ∀ v : V, v ^ 2 = 1)
    {G₁ G₂ J S X : Subgroup (MulAut V)} {U₁ U₂ : Subgroup V} (hJ : G₁ ⊔ G₂ = J)
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hs₁ : IsSimpleGroup ↥G₁)
    (hnab : ∃ a b : ↥G₁, a * b ≠ b * a) (hc₁ : Nat.card ↥G₁ = 168)
    (e₁ : ↥G₁ ≃* ↥(StatedSL 3 (ZMod 2)))
    (hdir : IsIntDirect (commV G₁) (commV G₂) (commV J)) (hc8 : Nat.card ↥(commV G₁) = 2 ^ 3)
    (hidx : (commV J ⊔ fixV J).index = 2) {s : MulAut V}
    (hs₂₁ : ∀ y ∈ G₂, s⁻¹ * y * s ∈ G₁) (hsJ : s ∈ Subgroup.normalizer (J : Set (MulAut V)))
    (hSn₁ : ∀ t ∈ S, t ∈ Subgroup.normalizer (G₁ : Set (MulAut V)))
    (hSn₂ : ∀ t ∈ S, t ∈ Subgroup.normalizer (G₂ : Set (MulAut V)))
    (hSC : ∀ t ∈ S, ∀ c ∈ fixV J, t c ∈ fixV J)
    (hXJ : X ≤ J) (hU₁ : U₁ ≤ commV G₁) (hU₂ : U₂ ≤ commV G₂)
    (hU₁8 : Nat.card ↥(U₁ ⊔ fixV J) = 8 * Nat.card ↥(fixV J))
    (hU₂8 : Nat.card ↥(U₂ ⊔ fixV J) = 8 * Nat.card ↥(fixV J))
    (hpt₁ : fixSec S (U₁ ⊔ fixV J) (fixV J) ≤ fixSec X (U₁ ⊔ fixV J) (fixV J))
    (hpt₂ : fixSec S (U₂ ⊔ fixV J) (fixV J) ≤ fixSec X (U₂ ⊔ fixV J) (fixV J))
    {g : MulAut V} (hgG : g ∈ G₁) (hgS : g ∈ S) (hg4 : orderOf g = 4) :
    fixSec S ⊤ (fixV J) ≤ fixSec X ⊤ (fixV J) := by
  subst hJ
  set C := fixV (G₁ ⊔ G₂) with hC
  set Y₁ := commV G₁ with hY₁
  set Y₂ := commV G₂ with hY₂
  obtain ⟨hY12, hinf12⟩ := hdir
  have hfixC : ∀ x ∈ G₁ ⊔ G₂, ∀ c ∈ C, x c = c := fun x hx c hc' => mem_fixV.mp hc' x hx
  have hn₂₁ : ∀ b ∈ G₂, ∀ x ∈ G₁, b * x * b⁻¹ ∈ G₁ := fun b hb x hx => by
    rw [← hc x hx b hb, mul_inv_cancel_right]
    exact hx
  have hn₁₂ : ∀ a ∈ G₁, ∀ y ∈ G₂, a * y * a⁻¹ ∈ G₂ := fun a ha y hy => by
    rw [hc a ha y hy, mul_inv_cancel_right]
    exact hy
  have hN₂₁ : ∀ b ∈ G₂, b ∈ Subgroup.normalizer (G₁ : Set (MulAut V)) := fun b hb =>
    LRed5.mem_normalizer_of_both (hn₂₁ b hb) (fun x hx => by
      simpa using hn₂₁ b⁻¹ (G₂.inv_mem hb) x hx)
  have hN₁₂ : ∀ a ∈ G₁, a ∈ Subgroup.normalizer (G₂ : Set (MulAut V)) := fun a ha =>
    LRed5.mem_normalizer_of_both (hn₁₂ a ha) (fun y hy => by
      simpa using hn₁₂ a⁻¹ (G₁.inv_mem ha) y hy)
  have hcen₂₁ : ∀ b ∈ G₂, ∀ y ∈ Y₁, b y = y := fun b hb y hy => by
    have h1 : b y * y⁻¹ ∈ Y₁ ⊓ Y₂ := ⟨Y₁.mul_mem
      (LRed4.commV_invariant_of_normalizer (hN₂₁ b hb) hy) (Y₁.inv_mem hy),
      Subgroup.subset_closure ⟨b, hb, y, rfl⟩⟩
    rw [hinf12, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  have hcen₁₂ : ∀ a ∈ G₁, ∀ y ∈ Y₂, a y = y := fun a ha y hy => by
    have h1 : a y * y⁻¹ ∈ Y₁ ⊓ Y₂ := ⟨Subgroup.subset_closure ⟨a, ha, y, rfl⟩,
      Y₂.mul_mem (LRed4.commV_invariant_of_normalizer (hN₁₂ a ha) hy) (Y₂.inv_mem hy)⟩
    rw [hinf12, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  have hnat₁ := binaryNaturalSL_of_card_eight hV2 hs₁ hnab hc₁ hc8
  have hCfix₁ : C ≤ fixV G₁ := fun c hc' =>
    mem_fixV.mpr fun a ha => mem_fixV.mp hc' a (Subgroup.mem_sup_left ha)
  have hY1C : Y₁ ⊓ C = ⊥ := by
    have h := FFC.B510.fixV_inf_eq_bot_of_natural (by norm_num) hnat₁
    exact le_bot_iff.mp fun y hy => h ▸ ⟨hCfix₁ hy.2, hy.1⟩
  have hY1C' : Y₁ ⊓ (Y₂ ⊔ C) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨y₂, hy₂, c, hc', rfl⟩ := Subgroup.mem_sup.mp hy2
    have hfy₂ : y₂ ∈ C := by
      refine mem_fixV_sup (mem_fixV.mpr fun a ha => hcen₁₂ a ha y₂ hy₂)
        (mem_fixV.mpr fun b hb => ?_)
      have h1 := hcen₂₁ b hb _ hy1
      rw [map_mul, hfixC b (Subgroup.mem_sup_right hb) c hc'] at h1
      exact mul_right_cancel h1
    have hyC : y₂ * c ∈ Y₁ ⊓ C := ⟨hy1, C.mul_mem hfy₂ hc'⟩
    rwa [hY1C] at hyC
  set C' := Y₂ ⊔ C with hC'
  have hfixC' : ∀ a ∈ G₁, ∀ c ∈ C', a c = c := by
    intro a ha c hc'
    obtain ⟨y₂, hy₂, c₀, hc₀, rfl⟩ := Subgroup.mem_sup.mp hc'
    rw [map_mul, hcen₁₂ a ha y₂ hy₂, hfixC a (Subgroup.mem_sup_left ha) c₀ hc₀]
  have hnat' : BinaryNaturalSL G₁ (Y₁ ⊔ C') C' 3 1 := by
    obtain ⟨K, hK, hfin, hcK, π, hπ⟩ := hnat₁
    refine ⟨K, hK, hfin, hcK, π, FFC.RealizesVia.extend hπ (fun h c hc' => ?_) ?_⟩
    · rw [hfixC' h h.2 c hc']
      exact hc'
    · exact hY1C'
  have hnat'' : BinaryNaturalSL G₁ (modComm G₁ ⊤ ⊔ C') C' 3 1 := by
    rw [modComm_top_eq]
    exact hnat'
  have hYeq : commV (G₁ ⊔ G₂) ⊔ C = Y₁ ⊔ C' := by rw [← hY12, sup_assoc]
  have hcardY : Nat.card ↥(Y₁ ⊔ C') = 8 * Nat.card ↥C' := by
    have h := card_sup_mul_card_inf Y₁ C'
    rw [hY1C', Subgroup.card_bot, mul_one, hc8] at h
    rw [h]
    norm_num
  have hcard16 : Nat.card ↥(⊤ : Subgroup V) = 2 ^ 4 * Nat.card ↥C' := by
    have h := Subgroup.index_mul_card (commV (G₁ ⊔ G₂) ⊔ C)
    rw [hidx, hYeq, hcardY] at h
    rw [Subgroup.card_top, ← h]
    ring
  have hsY : ∀ v, v ∈ Y₁ ⊔ C' → s v ∈ Y₁ ⊔ C' := fun v hv => by
    rw [← hYeq] at hv ⊢
    obtain ⟨a, ha, c, hc', rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul]
    exact Subgroup.mul_mem_sup (LRed4.commV_invariant_of_normalizer hsJ ha)
      (LRed5.fixV_invariant_of_normalizer hsJ hc')
  have hsY' : ∀ v, v ∈ Y₁ ⊔ C' → s⁻¹ v ∈ Y₁ ⊔ C' := fun v hv => by
    rw [← hYeq] at hv ⊢
    obtain ⟨a, ha, c, hc', rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul]
    exact Subgroup.mul_mem_sup (LRed4.commV_invariant_of_normalizer (Subgroup.inv_mem _ hsJ) ha)
      (LRed5.fixV_invariant_of_normalizer (Subgroup.inv_mem _ hsJ) hc')
  have hind : ¬ ∃ A B : Subgroup V, C' < A ∧ C' < B ∧ XMod.IsInv ↥G₁ A ∧ XMod.IsInv ↥G₁ B ∧
      A ⊔ B = ⊤ ∧ A ⊓ B = C' := by
    rintro ⟨A, B, hA, hB, hiA, hiB, hAB, hAB'⟩
    have hirr := FFC.irr_of_binaryNatural (by norm_num) hnat'
    have hinvY : ∀ x ∈ G₁, ∀ w ∈ Y₁ ⊔ C', x w ∈ Y₁ ⊔ C' := fun x hx w hw =>
      (hnat'.choose_spec.choose_spec.choose_spec.2.choose_spec).2.2.2.1 ⟨x, hx⟩ w hw
    have key : ∀ A' : Subgroup V, C' < A' → XMod.IsInv ↥G₁ A' → A' ⊓ (Y₁ ⊔ C') = C' →
        False := by
      intro A' hA' hiA' hmeet
      obtain ⟨u, huA, huC⟩ := IsConcreteLE.exists_of_lt hA'
      have huY : u ∉ Y₁ ⊔ C' := fun h => huC (hmeet ▸ ⟨huA, h⟩)
      have hu1 : u ∈ fixV G₁ := mem_fixV.mpr fun a ha => by
        have h1 : a u * u⁻¹ ∈ Y₁ ⊓ C' := by
          refine ⟨Subgroup.subset_closure ⟨a, ha, u, rfl⟩, ?_⟩
          rw [← hmeet]
          exact ⟨A'.mul_mem (hiA' ⟨a, ha⟩ u huA) (A'.inv_mem huA),
            Subgroup.mem_sup_left (Subgroup.subset_closure ⟨a, ha, u, rfl⟩)⟩
        rw [hY1C', Subgroup.mem_bot, mul_inv_eq_one] at h1
        exact h1
      have hu2 : s u ∈ fixV G₂ := mem_fixV.mpr fun b hb => by
        have h1 := mem_fixV.mp hu1 _ (hs₂₁ b hb)
        have e : b (s u) = s ((s⁻¹ * b * s) u) := by
          simp [MulAut.mul_apply]
        rw [e, h1]
      have hsuY : s u ∉ Y₁ ⊔ C' := fun h => huY (by simpa using hsY' _ h)
      have hY2 : (commV (G₁ ⊔ G₂) ⊔ C).index = 2 := hidx
      rw [hYeq] at hY2
      have hq : s u * u⁻¹ ∈ Y₁ ⊔ C' :=
        (Subgroup.mul_mem_iff_of_index_two hY2).mpr
          (iff_of_false hsuY fun h => huY (by simpa using (Y₁ ⊔ C').inv_mem h))
      obtain ⟨y₁, hy₁, c', hc', hq'⟩ := Subgroup.mem_sup.mp hq
      obtain ⟨y₂, hy₂, c, hc, rfl⟩ := Subgroup.mem_sup.mp hc'
      have hw : u * y₂ ∈ C := by
        refine mem_fixV_sup (mem_fixV.mpr fun a ha => ?_) (mem_fixV.mpr fun b hb => ?_)
        · rw [map_mul, mem_fixV.mp hu1 a ha, hcen₁₂ a ha y₂ hy₂]
        · have hsu : s u = y₁ * (y₂ * c) * u := mul_inv_eq_iff_eq_mul.mp hq'.symm
          have e : u * y₂ = s u * y₁⁻¹ * c⁻¹ := by
            rw [eq_comm, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, hsu]
            ac_rfl
          rw [e, map_mul, map_mul, map_inv, map_inv, mem_fixV.mp hu2 b hb, hcen₂₁ b hb y₁ hy₁,
            hfixC b (Subgroup.mem_sup_right hb) c hc]
      apply huY
      have : u = u * y₂ * y₂⁻¹ := by group
      rw [this]
      exact (Y₁ ⊔ C').mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_right hw))
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left (Y₂.inv_mem hy₂)))
    rcases hirr _ (fun x hx w hw => Subgroup.mem_inf.mpr ⟨hiA ⟨x, hx⟩ w hw.1, hinvY x hx w hw.2⟩)
      (le_inf hA.le le_sup_right) inf_le_right with h | h
    · exact key A hA hiA h
    · rcases hirr _ (fun x hx w hw => Subgroup.mem_inf.mpr ⟨hiB ⟨x, hx⟩ w hw.1,
        hinvY x hx w hw.2⟩) (le_inf hB.le le_sup_right) inf_le_right with h' | h'
      · exact key B hB hiB h'
      ·
        have hle : Y₁ ≤ C' := fun y hy => by
          rw [← hAB']
          exact ⟨(h.symm ▸ inf_le_left : Y₁ ⊔ C' ≤ A) (Subgroup.mem_sup_left hy),
            (h'.symm ▸ inf_le_left : Y₁ ⊔ C' ≤ B) (Subgroup.mem_sup_left hy)⟩
        have : Y₁ = ⊥ := le_bot_iff.mp (hY1C' ▸ le_inf le_rfl hle)
        rw [this, Subgroup.card_bot] at hc8
        norm_num at hc8
  have ha2 : orderOf (g ^ 2) = 2 := by
    rw [orderOf_pow' g two_ne_zero, hg4]
    norm_num
  have hfaith := faithful_of_natural (W := ⊤) hs₁ (fun _ _ _ _ => Subgroup.mem_top _) hfixC'
    hnat''
  have hmemY : ∀ w : V, (g ^ 2) w * w⁻¹ ∈ C → w ∈ Y₁ ⊔ C' := fun w hw => by
    have h := hB48 V hV2 G₁ ⊤ C' ⟨e₁⟩ le_top (fun _ _ _ => trivial)
      (fun a c hc' => by
        show (a : MulAut V) c ∈ C'
        rw [hfixC' a a.2 c hc']
        exact hc') hfaith hcard16 hind hnat'' (g ^ 2) (G₁.pow_mem hgG 2) ha2 w trivial
      (Subgroup.mem_sup_right hw)
    rwa [modComm_top_eq] at h
  have hU₁eq : U₁ ⊔ C = Y₁ ⊔ C := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le_sup_right hU₁ C) ?_
    have h := card_sup_mul_card_inf Y₁ C
    rw [hY1C, Subgroup.card_bot, mul_one, hc8] at h
    rw [hU₁8, h]
    norm_num
  have hY₂le : Nat.card ↥Y₂ ≤ 8 := by
    have hmap : ∀ y ∈ Y₂, s⁻¹ y ∈ Y₁ := fun y hy =>
      commV_le_of_swap (fun x hx => by simpa using hs₂₁ x hx) hy
    have h := Nat.card_le_card_of_injective (fun y : ↥Y₂ => (⟨s⁻¹ y, hmap y y.2⟩ : ↥Y₁))
      (fun a b hab => Subtype.ext (s⁻¹.injective (congrArg Subtype.val hab)))
    rw [hc8] at h
    simpa using h
  have hU₂eq : U₂ ⊔ C = Y₂ ⊔ C := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le_sup_right hU₂ C) ?_
    have h := card_sup_mul_card_inf Y₂ C
    have hpos : 0 < Nat.card ↥(Y₂ ⊓ C) := Nat.card_pos
    rw [hU₂8]
    calc Nat.card ↥(Y₂ ⊔ C) ≤ Nat.card ↥(Y₂ ⊔ C) * Nat.card ↥(Y₂ ⊓ C) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card ↥Y₂ * Nat.card ↥C := h
      _ ≤ 8 * Nat.card ↥C := Nat.mul_le_mul_right _ hY₂le
  have hmeet₁ : (Y₁ ⊔ C) ⊓ (C ⊔ (Y₂ ⊔ C)) = C := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right (le_sup_left))
    obtain ⟨y₁, hy₁, c₁, hc₁, rfl⟩ := Subgroup.mem_sup.mp hx.1
    have h2 : y₁ * c₁ ∈ Y₂ ⊔ C := by
      have := hx.2
      rwa [show C ⊔ (Y₂ ⊔ C) = Y₂ ⊔ C from sup_eq_right.mpr le_sup_right] at this
    have hy₁' : y₁ ∈ Y₁ ⊓ (Y₂ ⊔ C) := ⟨hy₁, by
      simpa using (Y₂ ⊔ C).mul_mem h2 (Subgroup.mem_sup_right (C.inv_mem hc₁))⟩
    rw [hY1C', Subgroup.mem_bot] at hy₁'
    rw [hy₁', one_mul]
    exact hc₁
  have hmeet₂ : (Y₂ ⊔ C) ⊓ (C ⊔ (Y₁ ⊔ C)) = C := by
    rw [show C ⊔ (Y₁ ⊔ C) = Y₁ ⊔ C from sup_eq_right.mpr le_sup_right, inf_comm,
      ← sup_eq_right.mpr (le_sup_right : C ≤ Y₂ ⊔ C)]
    simpa [sup_comm, sup_left_comm] using hmeet₁
  have hJN₁ : G₁ ⊔ G₂ ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) :=
    sup_le Subgroup.le_normalizer fun b hb => hN₂₁ b hb
  have hJN₂ : G₁ ⊔ G₂ ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) :=
    sup_le (fun a ha => hN₁₂ a ha) Subgroup.le_normalizer
  have hinvYC : ∀ x ∈ G₁ ⊔ G₂, (∀ v ∈ Y₁ ⊔ C, x v ∈ Y₁ ⊔ C) ∧
      ∀ v ∈ Y₂ ⊔ C, x v ∈ Y₂ ⊔ C := fun x hx => by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨a, ha, c, hc', rfl⟩ := Subgroup.mem_sup.mp hv
      rw [map_mul, hfixC x hx c hc']
      exact Subgroup.mul_mem_sup (LRed4.commV_invariant_of_normalizer (hJN₁ hx) ha) hc'
    · obtain ⟨a, ha, c, hc', rfl⟩ := Subgroup.mem_sup.mp hv
      rw [map_mul, hfixC x hx c hc']
      exact Subgroup.mul_mem_sup (LRed4.commV_invariant_of_normalizer (hJN₂ hx) ha) hc'
  rintro w ⟨-, hwS⟩
  refine ⟨trivial, fun x hx => ?_⟩
  have hwY := hmemY w (hwS _ (S.pow_mem hgS 2))
  obtain ⟨a₁, ha₁', a₂, ha₂, rfl⟩ := Subgroup.mem_sup.mp hwY
  have ha₁ : a₁ ∈ Y₁ ⊔ C := Subgroup.mem_sup_left ha₁'
  have hinvS : ∀ t ∈ S, (∀ v ∈ Y₁ ⊔ C, t v ∈ Y₁ ⊔ C) ∧ ∀ v ∈ Y₂ ⊔ C, t v ∈ Y₂ ⊔ C :=
    fun t ht => by
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · obtain ⟨a, ha, c, hc', rfl⟩ := Subgroup.mem_sup.mp hv
        rw [map_mul]
        exact Subgroup.mul_mem_sup (LRed4.commV_invariant_of_normalizer (hSn₁ t ht) ha)
          (hSC t ht c hc')
      · obtain ⟨a, ha, c, hc', rfl⟩ := Subgroup.mem_sup.mp hv
        rw [map_mul]
        exact Subgroup.mul_mem_sup (LRed4.commV_invariant_of_normalizer (hSn₂ t ht) ha)
          (hSC t ht c hc')
  have hS₁ : ∀ t ∈ S, t a₁ * a₁⁻¹ ∈ C := fun t ht =>
    mul_inv_mem_of_independent hmeet₁ (hinvS t ht).1 (hinvS t ht).2 ha₁ ha₂ (hwS t ht)
  have hS₂ : ∀ t ∈ S, t a₂ * a₂⁻¹ ∈ C := fun t ht =>
    mul_inv_mem_of_independent hmeet₂ (hinvS t ht).2 (hinvS t ht).1 ha₂ ha₁
      (by rw [mul_comm a₂ a₁]; exact hwS t ht)
  have hX₁ := (hpt₁ ⟨hU₁eq ▸ ha₁, hS₁⟩).2 x hx
  have hX₂ := (hpt₂ ⟨hU₂eq ▸ ha₂, hS₂⟩).2 x hx
  have e : x (a₁ * a₂) * (a₁ * a₂)⁻¹ = (x a₁ * a₁⁻¹) * (x a₂ * a₂⁻¹) := by
    rw [map_mul, mul_inv_rev]
    ac_rfl
  rw [e]
  exact C.mul_mem hX₁ hX₂

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
