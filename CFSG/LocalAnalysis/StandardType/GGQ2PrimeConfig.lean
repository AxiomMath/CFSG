module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeProp1012
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Reduced
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.Signalizers

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType
open scoped Pointwise

theorem mem_normalizer_of_map_conj_eq {Y : Type} [Group Y] {K : Subgroup Y} {g : Y}
    (hK : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ normalizer (K : Set Y) := by
  refine mem_normalizer_iff.2 fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · have : g * a * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := ⟨a, ha, by simp⟩
    rwa [hK] at this
  · rw [← hK] at ha
    obtain ⟨k, hk, hke⟩ := ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at hke
    exact hke ▸ hk

theorem normalizes_component {Y : Type} [Group Y]
    [Finite Y] {K W : Subgroup Y} (hK : CFSG.Open.IsComponentOf K ⊤) (hWK : W ≤ K)
    {a b : Y} (ha : a ∈ W) (hb : b ∈ W) (hab : a * b ≠ b * a) {g : Y}
    (hg : g ∈ normalizer (W : Set Y)) : g ∈ normalizer (K : Set Y) := by
  by_contra hgK
  have hne : K ≠ K.map (MulAut.conj g).toMonoidHom := fun h =>
    hgK (mem_normalizer_of_map_conj_eq h.symm)
  have hc' := CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK (mem_top g)
  have hb' : b ∈ K.map (MulAut.conj g).toMonoidHom := by
    refine ⟨g⁻¹ * b * g, hWK ?_, ?_⟩
    · have := (mem_normalizer_iff.1 (inv_mem hg) b).1 hb
      simpa using this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  exact hab (CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hK hc' hne (hWK ha) hb')

theorem conj_mem_centralizer_of_mem_normalizer {Y : Type} [Group Y] {K : Subgroup Y} {g s : Y}
    (hg : g ∈ normalizer (K : Set Y)) (hs : s ∈ centralizer (K : Set Y)) :
    g * s * g⁻¹ ∈ centralizer (K : Set Y) := by
  rw [mem_centralizer_iff] at hs ⊢
  intro k hk
  have hk' : g⁻¹ * k * g ∈ K := by simpa using (mem_normalizer_iff.1 (inv_mem hg) k).1 hk
  have := hs _ hk'
  calc k * (g * s * g⁻¹) = g * ((g⁻¹ * k * g) * s) * g⁻¹ := by group
    _ = g * (s * (g⁻¹ * k * g)) * g⁻¹ := by rw [this]
    _ = g * s * g⁻¹ * k := by group

theorem eq_of_invariant_four {Y : Type} [Group Y]
    [Finite Y] {T S : Subgroup Y} (hT : Nat.card T = 4) (hST : S ≤ T)
    {g : Y} (hgS : ∀ s ∈ S, g * s * g⁻¹ ∈ S) (hfpf : ∀ t ∈ T, g * t * g⁻¹ = t → t = 1)
    (hS : S ≠ ⊥) : S = T := by
  obtain ⟨⟨t, htS⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have huS : g * t * g⁻¹ ∈ S := hgS t htS
  have hut : g * t * g⁻¹ ≠ t := fun h => ht1' (hfpf t (hST htS) h)
  have hu1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply ht1'
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have h3 : ({1, t, g * t * g⁻¹} : Set Y).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨1, t, g * t * g⁻¹, ht1'.symm, hu1.symm, hut.symm, rfl⟩
  have hsub : ({1, t, g * t * g⁻¹} : Set Y) ⊆ (S : Set Y) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact S.one_mem
    · exact htS
    · exact huS
  have hle : 3 ≤ Nat.card S :=
    calc 3 = ({1, t, g * t * g⁻¹} : Set Y).ncard := h3.symm
      _ ≤ (S : Set Y).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card S := (Nat.card_coe_set_eq (S : Set Y)).symm
  have hdvd : Nat.card S ∣ 4 := hT ▸ card_dvd_of_le hST
  have h4 : Nat.card S = 4 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    rcases (show Nat.card S = 3 ∨ Nat.card S = 4 by omega) with h | h
    · rw [h] at hdvd; norm_num at hdvd
    · exact h
  exact eq_of_le_of_card_ge hST (by rw [hT, h4])

theorem o1ppMk_one {G : Type} [Group G] {x zn : G} : o1ppMk x zn (1 : G) = 1 := by
  rw [o1ppMk_of_mem (one_mem _)]
  rfl

theorem o1ppMk_mul {G : Type} [Group G] {x zn : G}
    {a b : G} (ha : a ∈ centralizer ({x * zn⁻¹} : Set G))
    (hb : b ∈ centralizer ({x * zn⁻¹} : Set G)) :
    o1ppMk x zn (a * b) = o1ppMk x zn a * o1ppMk x zn b := by
  rw [o1ppMk_of_mem ha, o1ppMk_of_mem hb, o1ppMk_of_mem (mul_mem ha hb), ← QuotientGroup.mk_mul]
  rfl

theorem o1ppMk_inv {G : Type} [Group G] {x zn : G}
    {a : G} (ha : a ∈ centralizer ({x * zn⁻¹} : Set G)) :
    o1ppMk x zn a⁻¹ = (o1ppMk x zn a)⁻¹ := by
  rw [o1ppMk_of_mem ha, o1ppMk_of_mem (inv_mem ha), ← QuotientGroup.mk_inv]
  rfl

theorem o1ppMk_mem_bar {G : Type} [Group G] {x zn : G}
    {W : Subgroup G} {a : G} (haH : a ∈ centralizer ({x * zn⁻¹} : Set G))
    (haW : a ∈ W) : o1ppMk x zn a ∈ O1ppXBar x zn W := by
  rw [o1ppMk_of_mem haH]
  exact ⟨⟨a, haH⟩, mem_subgroupOf.2 haW, rfl⟩

theorem exists_of_mem_bar {G : Type} [Group G] {x zn : G}
    {W : Subgroup G} {y : O1ppBar x zn} (hy : y ∈ O1ppXBar x zn W) :
    ∃ a ∈ W, ∃ haH : a ∈ centralizer ({x * zn⁻¹} : Set G), y = o1ppMk x zn a := by
  obtain ⟨w, hw, rfl⟩ := hy
  exact ⟨w, mem_subgroupOf.1 hw, w.2, by rw [o1ppMk_of_mem w.2]; rfl⟩

theorem o1ppMk_eq_iff {G : Type} [Group G] {x zn : G}
    {a b : G} (ha : a ∈ centralizer ({x * zn⁻¹} : Set G))
    (hb : b ∈ centralizer ({x * zn⁻¹} : Set G)) :
    o1ppMk x zn a = o1ppMk x zn b ↔ a⁻¹ * b ∈ O1ppCore x zn := by
  rw [o1ppMk_of_mem ha, o1ppMk_of_mem hb, QuotientGroup.eq]
  constructor
  · intro hm
    exact mem_map_of_mem _ hm
  · rintro ⟨c, hc', hce⟩
    have : c = (⟨a, ha⟩ : centralizer ({x * zn⁻¹} : Set G))⁻¹ * ⟨b, hb⟩ :=
      Subtype.ext (by simpa using hce)
    rwa [← this]

theorem o1ppMk_mem_normalizer {G : Type} [Group G] {x zn : G} {W : Subgroup G} {a : G}
    (haH : a ∈ centralizer ({x * zn⁻¹} : Set G)) (ha : a ∈ normalizer (W : Set G)) :
    o1ppMk x zn a ∈
      normalizer ((O1ppXBar x zn W : Subgroup (O1ppBar x zn)) : Set (O1ppBar x zn)) := by
  have hyN' : (⟨a, haH⟩ : centralizer ({x * zn⁻¹} : Set G)) ∈
      normalizer ((W.subgroupOf (centralizer ({x * zn⁻¹} : Set G)) : Subgroup _) : Set _) := by
    rw [mem_normalizer_iff]
    intro b
    simpa only [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv] using
      mem_normalizer_iff.1 ha (b : G)
  rw [o1ppMk_of_mem haH]
  exact le_normalizer_map _ (mem_map_of_mem _ hyN')

theorem o1ppMk_mem_centralizer {G : Type} [Group G] {x zn : G} {W : Subgroup G} {a : G}
    (haH : a ∈ centralizer ({x * zn⁻¹} : Set G)) (ha : ∀ w ∈ W, w * a = a * w) :
    o1ppMk x zn a ∈
      centralizer ((O1ppXBar x zn W : Subgroup (O1ppBar x zn)) : Set (O1ppBar x zn)) := by
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨w, hw, hwH, rfl⟩ := exists_of_mem_bar hy
  rw [← o1ppMk_mul hwH haH, ← o1ppMk_mul haH hwH, ha w hw]

theorem o1ppMk_mem_closure {G : Type} [Group G] {x zn : G}
    {s : Set G} (hs : s ⊆ centralizer ({x * zn⁻¹} : Set G)) {c : G}
    (hc : c ∈ closure s) :
    c ∈ centralizer ({x * zn⁻¹} : Set G) ∧ o1ppMk x zn c ∈ closure (o1ppMk x zn '' s) := by
  induction hc using Subgroup.closure_induction with
  | mem y hy => exact ⟨hs hy, subset_closure ⟨y, hy, rfl⟩⟩
  | one => exact ⟨one_mem _, by rw [o1ppMk_one]; exact one_mem _⟩
  | mul a b _ _ ha hb =>
    exact ⟨mul_mem ha.1 hb.1, by rw [o1ppMk_mul ha.1 hb.1]; exact mul_mem ha.2 hb.2⟩
  | inv a _ ha => exact ⟨inv_mem ha.1, by rw [o1ppMk_inv ha.1]; exact inv_mem ha.2⟩

theorem o1pp_X_inf_core {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (h : O1ppData B x zn L X Xk Tk) : X ⊓ O1ppCore x zn = ⊥ := by
  obtain ⟨hHO, hO3⟩ := o1pp_core_facts x zn
  obtain ⟨hXs, -, h3⟩ := o1pp_X_facts u52SimpleSix h
  have hXO : X ≤ normalizer ((O1ppCore x zn : Subgroup G) : Set G) := le_trans h.X_le hHO
  haveI := hXs
  haveI := normal_subgroupOf_of_le_normalizer hXO
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((O1ppCore x zn).subgroupOf X) with h' | h'
  · rw [subgroupOf_eq_bot] at h'
    exact disjoint_iff.1 h'.symm
  · rw [subgroupOf_eq_top] at h'
    have := Nat.Coprime.eq_one_of_dvd hO3 (h3.trans (card_dvd_of_le h'))
    omega

theorem o1pp_equiv_of_inf {G : Type} [Group G] {x zn : G}
    {W : Subgroup G} (hWH : W ≤ centralizer ({x * zn⁻¹} : Set G))
    (hWO : W ⊓ O1ppCore x zn = ⊥) : Nonempty (W ≃* O1ppXBar x zn W) := by
  set H := centralizer ({x * zn⁻¹} : Set G) with hH
  set π := QuotientGroup.mk' (LargeEvenPPrimeCore 3 ↥H) with hπdef
  set f : W →* O1ppBar x zn := π.comp (inclusion hWH) with hf
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hπdef, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    have hmem : (a : G) ∈ W ⊓ O1ppCore x zn := mem_inf.2 ⟨a.2, mem_map_of_mem _ ha⟩
    rw [hWO, mem_bot] at hmem
    rw [mem_bot]
    exact Subtype.ext hmem
  have hrange : f.range = O1ppXBar x zn W := by
    rw [hf, MonoidHom.range_comp, inclusion_range]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem o1pp_Tk_inf_core {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn zk : G}
    (h : O1ppDataK B x zn zk L X Xk Tk) : Tk ⊓ O1ppCore x zn = ⊥ := by
  obtain ⟨hBab, hxB, -⟩ := ggThmIHyp_unpack h.hyp
  have hxH := o1pp_B_le_H h.toO1ppData hxB
  obtain ⟨hHO, -⟩ := o1pp_core_facts x zn
  by_contra hne
  have heq : Tk ⊓ O1ppCore x zn = Tk := eq_of_invariant_four h.Tk_card inf_le_left
    (fun s hs => mem_inf.2 ⟨(mem_normalizer_iff.1 (h.B_norm_Tk hxB) s).1 (mem_inf.1 hs).1,
      (mem_normalizer_iff.1 (hHO hxH) s).1 (mem_inf.1 hs).2⟩) h.x_fpf hne
  apply prop_10_10 u52SimpleSix h.toO1ppData
  intro t ht
  have htO : t ∈ Tk ⊓ O1ppCore x zn := heq.symm ▸ ht
  exact le_normalizer (mem_sup_right (mem_inf.1 htO).2)

theorem o1pp_normalizes_XO {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (h : O1ppData B x zn L X Xk Tk) {t : G}
    (htH : t ∈ centralizer ({x * zn⁻¹} : Set G))
    (hτ : o1ppMk x zn t ∈
      normalizer ((O1ppXBar x zn X : Subgroup (O1ppBar x zn)) : Set (O1ppBar x zn))) :
    t ∈ normalizer ((X ⊔ O1ppCore x zn : Subgroup G) : Set G) := by
  obtain ⟨hHO, -⟩ := o1pp_core_facts x zn
  have hXO : X ≤ normalizer ((O1ppCore x zn : Subgroup G) : Set G) := le_trans h.X_le hHO
  apply mem_normalizer_of_conj_mem
  intro g hg
  obtain ⟨a, ha, o, ho, rfl⟩ := exists_mul_of_mem_sup hXO hg
  have hto : t * o * t⁻¹ ∈ O1ppCore x zn := (mem_normalizer_iff.1 (hHO htH) o).1 ho
  have haH := h.X_le ha
  have htaH : t * a * t⁻¹ ∈ centralizer ({x * zn⁻¹} : Set G) :=
    mul_mem (mul_mem htH haH) (inv_mem htH)
  have hta : o1ppMk x zn (t * a * t⁻¹) ∈ O1ppXBar x zn X := by
    rw [o1ppMk_mul (mul_mem htH haH) (inv_mem htH), o1ppMk_mul htH haH, o1ppMk_inv htH]
    exact (mem_normalizer_iff.1 hτ _).1 (o1ppMk_mem_bar haH ha)
  obtain ⟨a₂, ha₂X, ha₂H, he⟩ := exists_of_mem_bar hta
  have hk := (o1ppMk_eq_iff ha₂H htaH).1 he.symm
  have : t * (a * o) * t⁻¹ = a₂ * (a₂⁻¹ * (t * a * t⁻¹)) * (t * o * t⁻¹) := by group
  rw [this]
  exact mul_mem (mul_mem (mem_sup_left ha₂X) (mem_sup_right hk)) (mem_sup_right hto)

theorem o1pp_Xbar_facts {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (h : O1ppData B x zn L X Xk Tk) :
    (∃ a ∈ O1ppXBar x zn X, ∃ b ∈ O1ppXBar x zn X, a * b ≠ b * a) ∧
      center (O1ppXBar x zn X) = ⊥ := by
  obtain ⟨e⟩ := o1pp_X_equiv h
  obtain ⟨hXs, h2, h3⟩ := o1pp_X_facts u52SimpleSix h
  haveI := hXs
  obtain ⟨a, b, hab⟩ : ∃ a b : X, a * b ≠ b * a := exists_noncomm_of_simple Nat.prime_three h3
    (fun h' => by rw [h'] at h2; omega)
  haveI : IsSimpleGroup (O1ppXBar x zn X) := (MulEquiv.isSimpleGroup_congr e).1 hXs
  have hncb : ∃ a b : O1ppXBar x zn X, a * b ≠ b * a :=
    ⟨e a, e b, fun h' => hab (e.injective (by simpa [map_mul] using h'))⟩
  refine ⟨⟨(e a : O1ppBar x zn), (e a).2, (e b : O1ppBar x zn), (e b).2, fun h' => hab ?_⟩,
    center_eq_bot_of_noncomm hncb⟩
  apply e.injective
  apply Subtype.ext
  simpa [map_mul] using h'

theorem o1pp_Xkbar_facts {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn : G}
    (h : O1ppData B x zn L X Xk Tk) :
    Nonempty (Xk ≃* O1ppXBar x zn Xk) ∧
      ∃ a ∈ O1ppXBar x zn Xk, ∃ b ∈ O1ppXBar x zn Xk, a * b ≠ b * a := by
  have hXkO : Xk ⊓ O1ppCore x zn = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_right _ h.Xk_le).trans (o1pp_X_inf_core h).le)
  obtain ⟨e⟩ := o1pp_equiv_of_inf (h.Xk_le.trans h.X_le) hXkO
  refine ⟨⟨e⟩, ?_⟩
  obtain ⟨K, hF, hfin, hK, ⟨e4⟩⟩ := lieModel_PSU_four h.Xk_model
  obtain ⟨a, b, hab⟩ := u42Nonabelian K hF hfin hK
  refine ⟨(e (e4.symm a) : O1ppBar x zn), (e (e4.symm a)).2, (e (e4.symm b) : O1ppBar x zn),
    (e (e4.symm b)).2, fun h' => hab ?_⟩
  apply e4.symm.injective
  apply e.injective
  apply Subtype.ext
  simpa [map_mul] using h'

theorem o1pp_config {G : Type} [Group G] [Finite G] {B L X Xk Tk : Subgroup G} {x zn zk : G}
    (h : O1ppDataK B x zn zk L X Xk Tk) {K : Subgroup (O1ppBar x zn)}
    (hKc : CFSG.Open.IsComponentOf K ⊤) (hzN : o1ppMk x zn x ∈ normalizer (K : Set (O1ppBar x zn)))
    (hlt : O1ppXBar x zn X < K)
    (hXc : CFSG.Open.IsComponentOf (O1ppXBar x zn X)
      (K ⊓ centralizer ({o1ppMk x zn x} : Set (O1ppBar x zn))))
    (hlie : CFSG.StandardType.LargeEvenMarking K (fun _ _ _ _ _ _ => True)) :
    PumpUpConfig K (O1ppXBar x zn X) (O1ppXBar x zn Xk)
      (O1ppXBar x zn Tk) (O1ppXBar x zn B) (o1ppMk x zn x) (o1ppMk x zn zk)
      (o1ppMk x zn (x * zn⁻¹)) := by
  obtain ⟨hBab, hxB, -⟩ := ggThmIHyp_unpack h.hyp
  have hBH := o1pp_B_le_H h.toO1ppData
  have hxH := hBH hxB
  have hdB : x * zn⁻¹ ∈ B := mul_mem hxB (inv_mem h.zn_mem)
  have hdH := hBH hdB
  have hzkH := hBH h.zk_mem
  have hXx := o1pp_X_le_cx h.toO1ppData
  obtain ⟨eX⟩ := o1pp_X_equiv h.toO1ppData
  obtain ⟨⟨eXk⟩, a₀, ha₀, b₀, hb₀, hab₀⟩ := o1pp_Xkbar_facts h.toO1ppData
  obtain ⟨⟨a₁, ha₁, b₁, hb₁, hab₁⟩, hZX⟩ := o1pp_Xbar_facts h.toO1ppData
  have hTO := o1pp_Tk_inf_core h
  obtain ⟨eT⟩ := o1pp_equiv_of_inf h.Tk_le hTO
  have hTcard : Nat.card (O1ppXBar x zn Tk) = 4 := by
    rw [← Nat.card_congr eT.toEquiv]; exact h.Tk_card
  have hXkK : O1ppXBar x zn Xk ≤ K :=
    (map_mono (fun a ha => mem_subgroupOf.2 (h.Xk_le (mem_subgroupOf.1 ha)))).trans hlt.le
  have hzfpf : ∀ τ ∈ O1ppXBar x zn Tk, o1ppMk x zn x * τ * (o1ppMk x zn x)⁻¹ = τ → τ = 1 := by
    intro τ hτ hfix
    obtain ⟨t, ht, htH, rfl⟩ := exists_of_mem_bar hτ
    have hxtH : x * t * x⁻¹ ∈ centralizer ({x * zn⁻¹} : Set G) :=
      mul_mem (mul_mem hxH htH) (inv_mem hxH)
    have h1 : o1ppMk x zn (x * t * x⁻¹) = o1ppMk x zn t := by
      rw [o1ppMk_mul (mul_mem hxH htH) (inv_mem hxH), o1ppMk_mul hxH htH, o1ppMk_inv hxH]
      exact hfix
    have hmem := (o1ppMk_eq_iff hxtH htH).1 h1
    have hxtT : x * t * x⁻¹ ∈ Tk := (mem_normalizer_iff.1 (h.B_norm_Tk hxB) t).1 ht
    have hT' : (x * t * x⁻¹)⁻¹ * t ∈ Tk ⊓ O1ppCore x zn :=
      mem_inf.2 ⟨mul_mem (inv_mem hxtT) ht, hmem⟩
    rw [hTO, mem_bot, inv_mul_eq_one] at hT'
    rw [h.x_fpf t ht hT']
    exact o1ppMk_one
  have hzT : o1ppMk x zn x ∈ normalizer ((O1ppXBar x zn Tk : Subgroup _) : Set (O1ppBar x zn)) :=
    o1ppMk_mem_normalizer hxH (h.B_norm_Tk hxB)
  have hcl : closure {x, x * zn⁻¹} ≤ B := by
    rw [closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hxB
    · exact hdB
  have hdec : ∀ b ∈ B, ∃ e ∈ B ⊓ X, ∃ c ∈ closure {x, x * zn⁻¹}, e * c = b := by
    intro b hb
    rw [h.B_eq] at hb
    exact exists_mul_of_mem_sup
      (le_normalizer_of_commute fun e he c hc => elemAbelian_comm hBab (mem_inf.1 he).1 (hcl hc))
      hb
  have hclH : ({x, x * zn⁻¹} : Set G) ⊆ centralizer ({x * zn⁻¹} : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hxH
    · exact hdH
  have himg : ∀ c ∈ closure {x, x * zn⁻¹},
      o1ppMk x zn c ∈ closure {o1ppMk x zn x, o1ppMk x zn (x * zn⁻¹)} := by
    intro c hc
    have := (o1ppMk_mem_closure hclH hc).2
    rwa [Set.image_pair] at this
  have hzX : o1ppMk x zn x ∈ centralizer ((O1ppXBar x zn X : Subgroup _) : Set (O1ppBar x zn)) :=
    o1ppMk_mem_centralizer hxH fun w hw => mem_centralizer_singleton_iff.1 (hXx hw)
  have hdc := o1pp_d_center h.toO1ppData
  have hclB : closure {o1ppMk x zn x, o1ppMk x zn (x * zn⁻¹)} ≤ O1ppXBar x zn B := by
    rw [closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact o1ppMk_mem_bar hxH hxB
    · exact o1ppMk_mem_bar hdH hdB
  have hclC : closure {o1ppMk x zn x, o1ppMk x zn (x * zn⁻¹)} ≤
      centralizer ((O1ppXBar x zn X : Subgroup _) : Set (O1ppBar x zn)) := by
    rw [closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hzX
    · exact center_le_centralizer _ hdc
  refine ⟨hKc, hlie, hlt, hXc, h.X_model.of_mulEquiv eX,
    map_mono (fun a ha => mem_subgroupOf.2 (h.Xk_le (mem_subgroupOf.1 ha))),
    h.Xk_model.of_mulEquiv eXk, (h.Tk_two.comap_subtype).map _, hTcard, ?_, ?_, ?_,
    (hBab.subgroupOf _).map _, o1ppMk_mem_bar hxH hxB, o1ppMk_mem_bar hzkH h.zk_mem,
    o1ppMk_mem_bar hdH hdB, ?_, ?_, ?_, ?_, hdc, (o1pp_d_facts h.toO1ppData).2, hzfpf, ?_,
    o1pp_rank h.toO1ppData,
    o1ppMk_mem_centralizer hzkH fun w hw => mem_centralizer_iff.1 h.zk_Tk w hw, ?_,
    o1ppMk_mem_centralizer hzkH fun w hw => mem_centralizer_iff.1 h.zk_Xk w hw⟩
  · intro τ hτ
    obtain ⟨t, ht, htH, rfl⟩ := exists_of_mem_bar hτ
    exact normalizes_component hKc hXkK ha₀ hb₀ hab₀
      (o1ppMk_mem_normalizer htH (centralizer_le_normalizer _ (h.Tk_cent_Xk ht)))
  · by_contra hne
    have heq := eq_of_invariant_four hTcard inf_le_left
      (fun s hs => mem_inf.2 ⟨(mem_normalizer_iff.1 hzT s).1 (mem_inf.1 hs).1,
        conj_mem_centralizer_of_mem_normalizer hzN (mem_inf.1 hs).2⟩) hzfpf hne
    apply prop_10_10 u52SimpleSix h.toO1ppData
    intro t ht
    have htH := h.Tk_le ht
    have hτ : o1ppMk x zn t ∈ O1ppXBar x zn Tk ⊓ centralizer (K : Set (O1ppBar x zn)) :=
      heq.symm ▸ o1ppMk_mem_bar htH ht
    apply o1pp_normalizes_XO h.toO1ppData htH
    exact centralizer_le_normalizer _
      (centralizer_le (SetLike.coe_subset_coe.2 hlt.le) (mem_inf.1 hτ).2)
  · intro τ hτ
    obtain ⟨t, ht, htH, rfl⟩ := exists_of_mem_bar hτ
    exact o1ppMk_mem_centralizer htH fun w hw => mem_centralizer_iff.1 (h.Tk_cent_Xk ht) w hw
  · intro β hβ
    obtain ⟨b, hb, hbH, rfl⟩ := exists_of_mem_bar hβ
    have hbx : b ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.2 (elemAbelian_comm hBab hb hxB)
    exact normalizes_component hKc hlt.le ha₁ hb₁ hab₁
      (o1ppMk_mem_normalizer hbH (h.X_normal (mem_inf.2 ⟨hbx, hbH⟩)))
  · intro β hβ
    obtain ⟨b, hb, hbH, rfl⟩ := exists_of_mem_bar hβ
    exact o1ppMk_mem_normalizer hbH (h.B_norm_Tk hb)
  · refine le_antisymm (fun β hβ => ?_) (sup_le inf_le_left hclB)
    obtain ⟨b, hb, hbH, rfl⟩ := exists_of_mem_bar hβ
    obtain ⟨e, he, c, hc, rfl⟩ := hdec b hb
    have heH := hBH (mem_inf.1 he).1
    have hcH := hBH (hcl hc)
    rw [o1ppMk_mul heH hcH]
    exact mul_mem (mem_sup_left (mem_inf.2 ⟨o1ppMk_mem_bar heH (mem_inf.1 he).1,
      o1ppMk_mem_bar heH (mem_inf.1 he).2⟩)) (mem_sup_right (himg c hc))
  · refine le_antisymm (fun β hβ => ?_) (le_inf hclB hclC)
    obtain ⟨hβB, hβC⟩ := mem_inf.1 hβ
    obtain ⟨b, hb, hbH, rfl⟩ := exists_of_mem_bar hβB
    obtain ⟨e, he, c, hc, rfl⟩ := hdec b hb
    have heH := hBH (mem_inf.1 he).1
    have hcH := hBH (hcl hc)
    rw [o1ppMk_mul heH hcH] at hβC ⊢
    have hc' := himg c hc
    have heC :
        o1ppMk x zn e ∈ centralizer ((O1ppXBar x zn X : Subgroup _) : Set (O1ppBar x zn)) := by
      have := mul_mem hβC (inv_mem (hclC hc'))
      rwa [mul_inv_cancel_right] at this
    have heX : o1ppMk x zn e ∈ O1ppXBar x zn X := o1ppMk_mem_bar heH (mem_inf.1 he).2
    have hZ : (⟨o1ppMk x zn e, heX⟩ : O1ppXBar x zn X) ∈ center (O1ppXBar x zn X) :=
      mem_center_iff.2 fun w => Subtype.ext (mem_centralizer_iff.1 heC w w.2)
    rw [hZX, mem_bot] at hZ
    have he1 : o1ppMk x zn e = 1 := congrArg Subtype.val hZ
    rw [he1, one_mul]
    exact hc'
  · intro g hg3 hgC
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set H := centralizer ({x * zn⁻¹} : Set G) with hHdef
    have hBp : IsPGroup 3 (B.subgroupOf H) := hBab.isPGroup.comap_subtype
    have hcop : Nat.Coprime 3 (Nat.card (LargeEvenPPrimeCore 3 H)) :=
      CFSG.pPrimeCore_coprime_card (p := 3) (G := H)
    have hC := CFSG.LocalAnalysis.RankFourTheoremC.centralizer_map_mk
      (LargeEvenPPrimeCore 3 H) Nat.prime_three hcop hBp
    obtain ⟨c, hc, rfl⟩ := hC.le hgC
    have hn0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
    have hm := Nat.coprime_ordCompl Nat.prime_three hn0
    have hsplit := Nat.ordProj_mul_ordCompl_eq_self (orderOf c) 3
    generalize (orderOf c).factorization 3 = v at hm hsplit
    generalize orderOf c / 3 ^ v = m at hm hsplit
    have hm3 : ¬ 3 ∣ m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hm
    set π := QuotientGroup.mk' (LargeEvenPPrimeCore 3 H) with hπ
    have hpv : (c ^ m) ^ (3 ^ v) = 1 := by
      rw [← pow_mul, mul_comm, hsplit, pow_orderOf_eq_one]
    have hπ3 : π ((c ^ m) ^ 3) = 1 := by
      have hπc : π c ^ 3 = 1 := by
        have := pow_orderOf_eq_one (π c)
        rwa [hg3] at this
      rw [map_pow, map_pow, ← pow_mul, mul_comm, pow_mul, hπc, one_pow]
    have hcube : (c ^ m) ^ 3 = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπ3
      have h1 := Subgroup.orderOf_dvd_natCard _ hπ3
      have h2 : orderOf ((c ^ m) ^ 3) ∣ 3 ^ v := orderOf_dvd_of_pow_eq_one (by
        rw [← pow_mul, mul_comm, pow_mul, hpv, one_pow])
      have h3 : orderOf ((c ^ m) ^ 3) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 (hcop.pow_left v)) h1
      exact orderOf_eq_one_iff.1 h3
    have hcB : ((c ^ m : H) : G) ∈ B := by
      refine h.bstar.2.2.2 _ ?_ (by
        have := congrArg Subtype.val hcube
        simpa using this)
      rw [mem_centralizer_iff]
      intro b hb
      have hb' : (⟨b, hBH hb⟩ : H) ∈ B.subgroupOf H := mem_subgroupOf.2 hb
      have := mem_centralizer_iff.1 (pow_mem hc m) _ hb'
      exact congrArg Subtype.val this
    have hmm : m * m % 3 = 1 := by
      have : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases this with h' | h' <;> simp [Nat.mul_mod, h']
    have hgm : π c = (π c ^ m) ^ m := by
      calc π c = π c ^ 1 := (pow_one _).symm
        _ = π c ^ (m * m % orderOf (π c)) := by rw [hg3, hmm]
        _ = π c ^ (m * m) := pow_mod_orderOf _ _
        _ = (π c ^ m) ^ m := pow_mul _ _ _
    rw [hgm, ← map_pow]
    exact pow_mem (mem_map_of_mem _ (mem_subgroupOf.2 hcB)) m
  · intro g hg
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set H := centralizer ({x * zn⁻¹} : Set G) with hHdef
    set π := QuotientGroup.mk' (LargeEvenPPrimeCore 3 ↥H) with hπdef
    have hzk3 : ∃ n : ℕ, (⟨zk, hzkH⟩ : H) ^ 3 ^ n = 1 :=
      ⟨1, Subtype.ext (by simpa using hBab.2 zk h.zk_mem)⟩
    have hC := CFSG.ComponentClassification.LBalance.Quot.map_centralizer_eq (p := 3) hzk3
    rw [o1ppMk_of_mem hzkH] at hg
    have hg' : g ∈ (centralizer ({(⟨zk, hzkH⟩ : H)} : Set H)).map π := by
      rw [hπdef]; exact hC ▸ hg
    obtain ⟨y, hy, rfl⟩ := hg'
    have hyzk : (y : G) ∈ centralizer ({zk} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy)
    have := o1ppMk_mem_normalizer y.2 (h.zk_norm hyzk)
    rw [o1ppMk_of_mem y.2] at this
    exact this

end CFSG.GGQ2Prime
