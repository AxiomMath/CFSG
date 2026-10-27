module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SSplit
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRows

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429

theorem card_le_of_pRank_le {G : Type} [Group G] [Finite G] {n : ℕ}
    (h : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ n) {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := by
    refine IsPGroup.iff_orderOf.mpr fun x => ?_
    have hx : (x : G) ^ 3 = 1 := hE.2 x x.2
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hx))
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h3, pow_one]⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k} := by
    refine ⟨Nat.card G, fun j hj => ?_⟩
    obtain ⟨F, -, -, hF⟩ := hj
    have h1 : 3 ^ j ≤ Nat.card G := hF ▸ Subgroup.card_le_card_group F
    have h2 : j < 3 ^ j := Nat.lt_pow_self (by norm_num)
    omega
  have hmem : k ∈ {k | ∃ E : Subgroup G, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k} := ⟨E, le_top, hE, hk⟩
  have hkn : k ≤ n := (le_csSup hbdd hmem).trans h
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hkn

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem cubeInner_of_mulEquiv (e : X ≃* Y) (h : CubeInner Y) : CubeInner X := by
  intro τ hτ
  obtain ⟨y, hy⟩ := h (MulAut.congr e τ) (by rw [← map_pow, hτ, map_one])
  refine ⟨e.symm y, ?_⟩
  ext x
  have hx := congrArg (fun φ : MulAut Y => φ (e x)) hy
  change y * e x * y⁻¹ = e (τ (e.symm (e x))) at hx
  rw [MulEquiv.symm_apply_apply] at hx
  change e.symm y * x * (e.symm y)⁻¹ = τ x
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hx]

theorem isElemAbelian_map {E : Subgroup X} (f : X →* Y)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : CFSG.Assembly.IsElemAbelian 3 (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨a, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨b, ⟨z, hz, rfl⟩⟩ := b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [← map_pow, hE.2 x hx, map_one]

theorem isElemAbelian_mono {E F : Subgroup X} (hEF : E ≤ F)
    (hF : CFSG.Assembly.IsElemAbelian 3 F) : CFSG.Assembly.IsElemAbelian 3 E := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hF.2 x (hEF hx)⟩
  show (a : X) * b = b * a
  exact congrArg Subtype.val (hF.1.is_comm.comm ⟨a, hEF a.2⟩ ⟨b, hEF b.2⟩)

theorem isElemAbelian_comap {E : Subgroup Y} (f : X →* Y) (hf : Function.Injective f)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : CFSG.Assembly.IsElemAbelian 3 (E.comap f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩)
  · rw [map_pow, hE.2 _ hx, map_one]

@[expose] def E9Move (S : Type) [Group S] : Prop :=
  ∀ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 → ∀ s ∈ E, s ≠ 1 →
    ∃ n ∈ Subgroup.normalizer (E : Set S),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S)

theorem E9Move.of_mulEquiv (e : X ≃* Y) (h : E9Move Y) : E9Move X := by
  intro E hE hE9 s hs hs1
  have hEm : CFSG.Assembly.IsElemAbelian 3 (E.map e.toMonoidHom) := isElemAbelian_map _ hE
  obtain ⟨n, hn, hns⟩ := h (E.map e.toMonoidHom) hEm
    (by rw [Subgroup.card_map_of_injective e.injective, hE9]) (e s) ⟨s, hs, rfl⟩
    (by rw [Ne, map_eq_one_iff _ e.injective]; exact hs1)
  have hN := Subgroup.map_equiv_normalizer_eq E e
  rw [← hN] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  refine ⟨m, hm, fun hm' => hns ?_⟩
  have hZ : (Subgroup.zpowers s).map e.toMonoidHom = Subgroup.zpowers (e s) :=
    MonoidHom.map_zpowers _ s
  rw [← hZ, ← Subgroup.map_equiv_normalizer_eq]
  exact ⟨m, hm', rfl⟩

end Transport

section Split

variable {G : Type} [Group G] [Finite G]

theorem inner_split_of {L A : Subgroup G} (hZ : Subgroup.center L = ⊥) (hcube : CubeInner L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA : Late.IsE27 A)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 3)
    (h9 : ∀ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hE9 : ∃ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9) :
    Nat.card (A ⊓ L : Subgroup G) = 9 ∧
      Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) = 3 ∧
      (A ⊓ L) ⊔ (A ⊓ Subgroup.centralizer (L : Set G)) = A := by
  refine inner_split hZ hcube hAN hA (fun E hE => card_le_of_pRank_le h3.le hE) ?_ ?_
  · intro E hEL hE
    have hE' : CFSG.Assembly.IsElemAbelian 3 (E.subgroupOf L) :=
      isElemAbelian_comap L.subtype L.subtype_injective hE
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv]
    exact h9 _ hE'
  · obtain ⟨E, hE, hE9⟩ := hE9
    refine ⟨E.map L.subtype, Subgroup.map_subtype_le E, isElemAbelian_map _ hE, ?_⟩
    rw [Subgroup.card_map_of_injective L.subtype_injective, hE9]

theorem mem_normalizer_of_split {L A : Subgroup G}
    (hsplit : (A ⊓ L) ⊔ (A ⊓ Subgroup.centralizer (L : Set G)) = A) {n : G} (hnL : n ∈ L)
    (hn : n ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G)) :
    n ∈ Subgroup.normalizer (A : Set G) := by
  set A' := A.map (MulAut.conj n).toMonoidHom with hA'
  have hinj : Function.Injective (MulAut.conj n).toMonoidHom := (MulAut.conj n).injective
  have hle : A ≤ A' := by
    rw [← hsplit]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · have hx' : n⁻¹ * x * n⁻¹⁻¹ ∈ A ⊓ L :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x).mp hx
      refine ⟨n⁻¹ * x * n⁻¹⁻¹, hx'.1, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    · refine ⟨x, hx.1, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hc : n * x = x * n := Subgroup.mem_centralizer_iff.mp hx.2 n hnL
      rw [hc, mul_inv_cancel_right]
  have heq : A' = A := (Subgroup.eq_of_le_of_card_ge hle
    (by rw [hA', Subgroup.card_map_of_injective hinj])).symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : (MulAut.conj n).toMonoidHom x ∈ A' := ⟨x, hx, rfl⟩
    rw [heq] at this
    simpa using this
  · intro hx
    have hx' : (MulAut.conj n).toMonoidHom x ∈ A' := by
      rw [heq]
      simpa using hx
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [hinj hyx] at hy

theorem zpowers_subgroupOf {L : Subgroup G} {c : G} (hcL : c ∈ L) :
    (Subgroup.zpowers c).subgroupOf L = Subgroup.zpowers (⟨c, hcL⟩ : L) := by
  have hmap : (Subgroup.zpowers (⟨c, hcL⟩ : L)).map L.subtype = Subgroup.zpowers c :=
    MonoidHom.map_zpowers _ _
  rw [← hmap]
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

theorem mem_normalizer_of_subgroupOf {L H : Subgroup G} (hHL : H ≤ L) {n : L}
    (hn : n ∈ Subgroup.normalizer ((H.subgroupOf L : Subgroup L) : Set L)) :
    (n : G) ∈ Subgroup.normalizer (H : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hHL] at hn
  exact hn

theorem mem_normalizer_subgroupOf {L H : Subgroup G} (hHL : H ≤ L) {n : L}
    (hn : (n : G) ∈ Subgroup.normalizer (H : Set G)) :
    n ∈ Subgroup.normalizer ((H.subgroupOf L : Subgroup L) : Set L) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hHL]
  exact hn

theorem false_of_e9Move {L A : Subgroup G} (hZ : Subgroup.center L = ⊥) (hcube : CubeInner L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA : Late.IsE27 A)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 3)
    (h9 : ∀ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hE9 : ∃ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hmove : E9Move L) {c : G} (hcA : c ∈ A) (hcL : c ∈ L) (hc1 : c ≠ 1)
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    False := by
  obtain ⟨hAL9, -, hsplit⟩ := inner_split_of hZ hcube hAN hA h3 h9 hE9
  set E : Subgroup L := (A ⊓ L).subgroupOf L with hE
  have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
    isElemAbelian_comap L.subtype L.subtype_injective (isElemAbelian_mono inf_le_left hA.1)
  have hEcard : Nat.card E = 9 := by
    rw [hE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv,
      hAL9]
  have hsE : (⟨c, hcL⟩ : L) ∈ E := ⟨hcA, hcL⟩
  have hs1 : (⟨c, hcL⟩ : L) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  obtain ⟨n, hn, hns⟩ := hmove E hEab hEcard _ hsE hs1
  have hnA : (n : G) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    mem_normalizer_of_subgroupOf inf_le_right hn
  have hnAA := mem_normalizer_of_split hsplit n.2 hnA
  apply hns
  rw [← zpowers_subgroupOf hcL]
  exact mem_normalizer_subgroupOf (Subgroup.zpowers_le.mpr hcL) (hN hnAA)

theorem mem_normalizer_sup {H K : Subgroup G} {n : G}
    (hH : n ∈ Subgroup.normalizer (H : Set G)) (hK : n ∈ Subgroup.normalizer (K : Set G)) :
    n ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  have hmap : ∀ {X : Subgroup G}, n ∈ Subgroup.normalizer (X : Set G) →
      X.map (MulAut.conj n).toMonoidHom = X := by
    intro X hX
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hX y).mp hy
    · intro hx
      refine ⟨n⁻¹ * x * n⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hX) x).mp hx,
        ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
  have heq : (H ⊔ K).map (MulAut.conj n).toMonoidHom = H ⊔ K := by
    rw [Subgroup.map_sup, hmap hH, hmap hK]
  have hinj : Function.Injective (MulAut.conj n).toMonoidHom := (MulAut.conj n).injective
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : (MulAut.conj n).toMonoidHom x ∈ (H ⊔ K).map (MulAut.conj n).toMonoidHom := ⟨x, hx, rfl⟩
    rw [heq] at this
    simpa using this
  · intro hx
    have hx' : (MulAut.conj n).toMonoidHom x ∈ (H ⊔ K).map (MulAut.conj n).toMonoidHom := by
      rw [heq]
      simpa using hx
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [hinj hyx] at hy

theorem mem_normalizer_of_le_centralizer {L B : Subgroup G}
    (hB : B ≤ Subgroup.centralizer (L : Set G)) {n : G} (hn : n ∈ L) :
    n ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hc : n * x = x * n := Subgroup.mem_centralizer_iff.mp (hB hx) n hn
    rw [hc, mul_inv_cancel_right]
    exact hx
  · intro hx
    have hc : n * x * n⁻¹ * n = n * (n * x * n⁻¹) := by
      have := Subgroup.mem_centralizer_iff.mp (hB hx) n hn
      rw [this]
    have : x = n * x * n⁻¹ := by
      calc x = n⁻¹ * (n * x * n⁻¹ * n) := by group
        _ = n⁻¹ * (n * (n * x * n⁻¹)) := by rw [hc]
        _ = n * x * n⁻¹ := by group
    rw [this]
    exact hx

theorem exists_e27_of_move {L A K' F : Subgroup G} (hZ : Subgroup.center L = ⊥) (hK'L : K' ≤ L)
    (hA : Late.IsE27 A)
    (hB3 : Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) = 3)
    (hFK : F ≤ K') (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9)
    {n c : G} (hnL : n ∈ L) (hnF : n ∈ Subgroup.normalizer (F : Set G))
    (hnc : n ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    ∃ E : Subgroup G, E ≤ K' ⊔ (A ⊓ Subgroup.centralizer (K' : Set G)) ∧ Late.IsE27 E ∧
      ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  set B := A ⊓ Subgroup.centralizer (L : Set G) with hBdef
  have hFL : F ≤ L := hFK.trans hK'L
  have hBK' : B ≤ A ⊓ Subgroup.centralizer (K' : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le hK'L)
  have hcomm : ∀ x ∈ F, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp hy.2 x (hFL hx))
  have hBab : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_mono inf_le_left hA.1
  have hinf : F ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxF, hxB⟩
    rw [Subgroup.mem_bot]
    have hxZ : (⟨x, hFL hxF⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxB.2 g g.2)
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact congrArg Subtype.val hxZ
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute F B hcomm)
  refine ⟨F ⊔ B, sup_le_sup hFK hBK', ⟨Sec13.isElemAbelian_sup hF hBab hcomm, ?_⟩, ?_⟩
  · have h1 := hcard.1
    rw [hinf, Subgroup.card_bot, mul_one, hF9, hB3] at h1
    exact h1
  · intro hle
    exact hnc (hle (mem_normalizer_sup hnF (mem_normalizer_of_le_centralizer inf_le_right hnL)))

end Split

@[expose] def SurvJ2 (S : Type) [Group S] : Prop :=
  ∀ (s : S) (K : Subgroup S), CC425 s K →
    IsExtOf K (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3))

@[expose] def SurvE (S T : Type) [Group S] [Group T] : Prop :=
  ∀ (s : S) (K : Subgroup S), CC425 s K →
    IsExtOf K T (Multiplicative (ZMod 3)) ∧
      ∃ F : Subgroup S, F ≤ K ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 ∧
        ∃ n ∈ Subgroup.normalizer (F : Set S),
          n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S)

section Rows


variable {G : Type} [Group G] [Finite G]

theorem cc425_of_row {S : Type} [Group S] (hθ : aschbacherSolvableCore 3 G = ⊥)
    {A L : Subgroup G} (hA : Late.IsE27 A) (hL : IsComponent L) (hZ : Subgroup.center L = ⊥)
    (e : L ⧸ Subgroup.center L ≃* S) {c : G} (hLc : ¬ L ≤ Subgroup.centralizer {c})
    {K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G)} (hK : IsComponent K)
    {K' : Subgroup G} (hK' : K' = K.map (L ⊓ Subgroup.centralizer {c}).subtype)
    (htype : IsType425 (K ⧸ aschbacherSolvableCore 3 K))
    (hAZ : A ⊓ (K' ⊓ Subgroup.centralizer (K' : Set G)) = Subgroup.zpowers c) :
    ∃ hc : c ∈ L, CC425 (((quotCenterEquivOfEqBot hZ).trans e) ⟨c, hc⟩)
      ((K'.subgroupOf L).map (((quotCenterEquivOfEqBot hZ).trans e : L ≃* S) : L →* S)) := by
  haveI : Finite S := Finite.of_equiv _ e.toEquiv
  obtain ⟨hc, -, hcc⟩ := exists_cc425 hθ hA hL hLc hK hK' htype hAZ
  refine ⟨hc, ?_⟩
  have hmap := hcc.map e
  have heq : ((K'.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L))).map
      (e : L ⧸ Subgroup.center L →* S) =
        (K'.subgroupOf L).map (((quotCenterEquivOfEqBot hZ).trans e : L ≃* S) : L →* S) := by
    rw [Subgroup.map_map]
    rfl
  rw [heq] at hmap
  exact hmap

@[expose] noncomputable def equivImage {S : Type} [Group S] {L : Subgroup G} (eL : L ≃* S)
    {c : G} {K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G)} {K' : Subgroup G}
    (hK' : K' = K.map (L ⊓ Subgroup.centralizer {c}).subtype) (hK'L : K' ≤ L) :
    K ≃* (K'.subgroupOf L).map (eL : L →* S) :=
  ((K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'.symm)).trans
    ((Subgroup.subgroupOfEquivOfLe hK'L).symm.trans
      ((K'.subgroupOf L).equivMapOfInjective _ eL.injective))

theorem le_normalizer_of_item45
    (hG : SectionFourHyp G) {A L : Subgroup G} (hA : Late.IsE27 A)
    (hL : IsComponent L) : A ≤ Subgroup.normalizer (L : Set G) :=
  rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
    (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L (mem_thetaComponents_of_isComponent3 hL)

structure RankTwoData (S : Type) [Group S] : Prop where
  cubeInner : CubeInner S
  card_le : ∀ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9
  exists_e9 : ∃ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9

theorem RankTwoData.transport
    {S : Type} [Group S] {L : Subgroup G} (eL : L ≃* S)
    (h : RankTwoData S) :
    CubeInner L ∧ (∀ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9) ∧
      ∃ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  refine ⟨cubeInner_of_mulEquiv eL h.cubeInner, fun E hE => ?_, ?_⟩
  · have := h.card_le (E.map eL.toMonoidHom) (isElemAbelian_map _ hE)
    rwa [Subgroup.card_map_of_injective eL.injective] at this
  · obtain ⟨E, hE, hE9⟩ := h.exists_e9
    exact ⟨E.map eL.symm.toMonoidHom, isElemAbelian_map _ hE,
      by rw [Subgroup.card_map_of_injective eL.symm.injective, hE9]⟩

theorem row425_of_e9Move
    {S : Type} [Group S] [Finite S]
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* S) →
      Subgroup.center L = ⊥)
    (hR : RankTwoData S) (hmove : E9Move S) : Row425 S := by
  intro G _ _ hG A hA h3 hθ L hL ⟨e⟩ c hLc K hK K' hK' htype hAZ hN
  exfalso
  have hZ : Subgroup.center L = ⊥ :=
    hZS L (sectionFourHyp_subgroup hG L) hL.1 (isPGroup_center_of_isComponent hθ hL) ⟨e⟩
  set eL : L ≃* S := (quotCenterEquivOfEqBot hZ).trans e
  obtain ⟨hcL, -⟩ := cc425_of_row hθ hA hL hZ e hLc hK hK' htype hAZ
  have hcA : c ∈ A := (hAZ ▸ Subgroup.mem_zpowers c :
    c ∈ A ⊓ (K' ⊓ Subgroup.centralizer (K' : Set G))).1
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hLc fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
  obtain ⟨hcube, h9, hE9⟩ := hR.transport eL
  exact false_of_e9Move hZ hcube (le_normalizer_of_item45 hG hA hL) hA h3 h9 hE9
    (hmove.of_mulEquiv eL) hcA hcL hc1 hN

theorem row425_of_survJ2
    {S : Type} [Group S] [Finite S]
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* S) →
      Subgroup.center L = ⊥)
    (hX : Nonempty (S ≃* Blueprint.NativeSporadic.J2)) (hsurv : SurvJ2 S) : Row425 S := by
  intro G _ _ hG A hA h3 hθ L hL ⟨e⟩ c hLc K hK K' hK' htype hAZ hN
  have hZ : Subgroup.center L = ⊥ :=
    hZS L (sectionFourHyp_subgroup hG L) hL.1 (isPGroup_center_of_isComponent hθ hL) ⟨e⟩
  set eL : L ≃* S := (quotCenterEquivOfEqBot hZ).trans e
  obtain ⟨hcL, hcc⟩ := cc425_of_row hθ hA hL hZ e hLc hK hK' htype hAZ
  have hK'L : K' ≤ L := hK' ▸ (Subgroup.map_subtype_le K).trans inf_le_left
  obtain ⟨φ⟩ := hX
  exact Or.inl ⟨isExtOf_congr (equivImage eL hK' hK'L).symm (hsurv _ _ hcc), ⟨eL.trans φ⟩⟩

theorem exists_move_of_image
    {S : Type} [Group S] {L K' : Subgroup G} (eL : L ≃* S)
    (hK'L : K' ≤ L) {c : G} (hcL : c ∈ L) {F : Subgroup S}
    (hFK : F ≤ (K'.subgroupOf L).map (eL : L →* S)) (hF : CFSG.Assembly.IsElemAbelian 3 F)
    (hF9 : Nat.card F = 9) {n : S} (hn : n ∈ Subgroup.normalizer (F : Set S))
    (hns : n ∉ Subgroup.normalizer (Subgroup.zpowers (eL ⟨c, hcL⟩) : Set S)) :
    ∃ FG : Subgroup G, FG ≤ K' ∧ CFSG.Assembly.IsElemAbelian 3 FG ∧ Nat.card FG = 9 ∧
      ∃ m ∈ L, m ∈ Subgroup.normalizer (FG : Set G) ∧
        m ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  set FL : Subgroup L := F.map (eL.symm : S →* L) with hFL
  have hFLK : FL ≤ K'.subgroupOf L := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hFK hy
    simpa using hx
  set FG : Subgroup G := FL.map L.subtype with hFG
  have hFGL : FG ≤ L := Subgroup.map_subtype_le FL
  have hFGsub : FG.subgroupOf L = FL := Subgroup.comap_map_eq_self_of_injective
    L.subtype_injective FL
  set m : L := eL.symm n with hm
  have hmFL : m ∈ Subgroup.normalizer (FL : Set L) := by
    have h := Subgroup.map_equiv_normalizer_eq F eL.symm
    have : m ∈ (Subgroup.normalizer (F : Set S)).map eL.symm.toMonoidHom := ⟨n, hn, rfl⟩
    rw [h] at this
    exact this
  refine ⟨FG, ?_, isElemAbelian_map _ (isElemAbelian_map _ hF), ?_, (m : G), m.2, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hFLK hy
  · rw [hFG, Subgroup.card_map_of_injective L.subtype_injective, hFL,
      Subgroup.card_map_of_injective eL.symm.injective, hF9]
  · exact mem_normalizer_of_subgroupOf hFGL (by rw [hFGsub]; exact hmFL)
  · intro hmc
    have h1 : m ∈ Subgroup.normalizer ((Subgroup.zpowers (⟨c, hcL⟩ : L)) : Set L) := by
      rw [← zpowers_subgroupOf hcL]
      exact mem_normalizer_subgroupOf (Subgroup.zpowers_le.mpr hcL) hmc
    apply hns
    have h := Subgroup.map_equiv_normalizer_eq (Subgroup.zpowers (⟨c, hcL⟩ : L)) eL
    have hZ : (Subgroup.zpowers (⟨c, hcL⟩ : L)).map eL.toMonoidHom =
        Subgroup.zpowers (eL ⟨c, hcL⟩) := MonoidHom.map_zpowers _ _
    rw [hZ] at h
    rw [← h]
    exact ⟨m, h1, by simp [hm]⟩

theorem row425_of_survE
    {S : Type} [Group S] [Finite S]
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* S) →
      Subgroup.center L = ⊥)
    (hR : RankTwoData S)
    (hT : (Nonempty (S ≃* Blueprint.NativeSporadic.M24) ∧ SurvE S (alternatingGroup (Fin 6))) ∨
      (Nonempty (S ≃* Blueprint.NativeSporadic.He) ∧ SurvE S (alternatingGroup (Fin 7)))) :
    Row425 S := by
  intro G _ _ hG A hA h3 hθ L hL ⟨e⟩ c hLc K hK K' hK' htype hAZ hN
  have hZ : Subgroup.center L = ⊥ :=
    hZS L (sectionFourHyp_subgroup hG L) hL.1 (isPGroup_center_of_isComponent hθ hL) ⟨e⟩
  set eL : L ≃* S := (quotCenterEquivOfEqBot hZ).trans e
  obtain ⟨hcL, hcc⟩ := cc425_of_row hθ hA hL hZ e hLc hK hK' htype hAZ
  have hK'L : K' ≤ L := hK' ▸ (Subgroup.map_subtype_le K).trans inf_le_left
  obtain ⟨hcube, h9, hE9⟩ := hR.transport eL
  obtain ⟨-, hB3, -⟩ := inner_split_of hZ hcube (le_normalizer_of_item45 hG hA hL) hA h3 h9 hE9
  right
  right
  rcases hT with ⟨⟨φ⟩, hsurv⟩ | ⟨⟨φ⟩, hsurv⟩
  · obtain ⟨hext, F, hFK, hF, hF9, n, hn, hns⟩ := hsurv _ _ hcc
    obtain ⟨FG, hFGK, hFG, hFG9, m, hmL, hmF, hmc⟩ :=
      exists_move_of_image eL hK'L hcL hFK hF hF9 hn hns
    obtain ⟨E, hE1, hE2, hE3⟩ := exists_e27_of_move hZ hK'L hA hB3 hFGK hFG hFG9 hmL hmF hmc
    exact ⟨Or.inl ⟨isExtOf_congr (equivImage eL hK' hK'L).symm hext, ⟨eL.trans φ⟩⟩,
      E, hE1, hE2, hE3⟩
  · obtain ⟨hext, F, hFK, hF, hF9, n, hn, hns⟩ := hsurv _ _ hcc
    obtain ⟨FG, hFGK, hFG, hFG9, m, hmL, hmF, hmc⟩ :=
      exists_move_of_image eL hK'L hcL hFK hF hF9 hn hns
    obtain ⟨E, hE1, hE2, hE3⟩ := exists_e27_of_move hZ hK'L hA hB3 hFGK hFG hFG9 hmL hmF hmc
    exact ⟨Or.inr ⟨isExtOf_congr (equivImage eL hK' hK'L).symm hext, ⟨eL.trans φ⟩⟩,
      E, hE1, hE2, hE3⟩

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
