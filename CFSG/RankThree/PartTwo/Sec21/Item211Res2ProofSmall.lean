module

public import CFSG.RankThree.PartTwo.Sec21.Item211ProofList
import CFSG.RankThree.PartTwo.Sec21.Item22Equivariance
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
import CFSG.RankThree.PartTwo.Sec4.Item462ProofCent
import CFSG.RankThree.PartTwo.Sec4.Item423StepsProofConfig
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

open CFSG.Blueprint
open scoped commutatorElement

namespace Item211Res2Proof

section Count

variable {H : Type*} [Group H] [Finite H]

theorem five_le_card_of_not_commute {T U : Subgroup H} {b : H} (hb3 : b ^ 3 = 1)
    (hbT : ∀ s ∈ T, b * s * b⁻¹ ∈ T) (hUT : U ≤ T) (hUb : ∀ u ∈ U, b * u * b⁻¹ = u)
    (hU : U ≠ ⊥) {t : H} (htT : t ∈ T) (ht : b * t * b⁻¹ ≠ t) : 5 ≤ Nat.card T := by
  classical
  obtain ⟨u, huU, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    obtain ⟨⟨u, huU⟩, hu⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU
    exact ⟨u, huU, fun h => hu (Subtype.ext h)⟩
  set κ : MulAut H := MulAut.conj b with hκ
  have hκa : ∀ s, κ s = b * s * b⁻¹ := fun s => rfl
  have hκinj : ∀ x y, κ x = κ y → x = y := fun x y h => κ.injective h
  have hκ3 : ∀ s, κ (κ (κ s)) = s := by
    intro s
    have h3 : κ ^ 3 = 1 := by rw [hκ, ← map_pow, hb3, map_one]
    have : (κ ^ 3) s = κ (κ (κ s)) := by
      rw [pow_three]
      rfl
    rw [← this, h3]
    rfl
  set t₁ := κ t with ht₁
  set t₂ := κ t₁ with ht₂
  have hκt₂ : κ t₂ = t := hκ3 t
  have hf1 : κ 1 = 1 := map_one κ
  have hfu : κ u = u := by rw [hκa]; exact hUb u huU
  have hm : κ t ≠ t := by rw [hκa]; exact ht
  have hm₁ : κ t₁ ≠ t₁ := fun h => hm (hκinj t₁ t h)
  have hm₂ : κ t₂ ≠ t₂ := by
    intro h
    rw [hκt₂] at h
    apply hm
    have h' : κ t = κ t₂ := by rw [← h]
    rw [h', hκt₂]
  have hne : ∀ x y, κ x = x → κ y ≠ y → x ≠ y := fun x y hx hy hxy => hy (hxy ▸ hx)
  have h01 : (1 : H) ≠ u := fun h => hu1 h.symm
  have h0t := hne 1 t hf1 hm
  have h0t₁ := hne 1 t₁ hf1 hm₁
  have h0t₂ := hne 1 t₂ hf1 hm₂
  have hut := hne u t hfu hm
  have hut₁ := hne u t₁ hfu hm₁
  have hut₂ := hne u t₂ hfu hm₂
  have htt₁ : t ≠ t₁ := fun h => hm h.symm
  have htt₂ : t ≠ t₂ := by
    intro h
    apply hm
    calc κ t = κ t₂ := by rw [← h]
      _ = t := hκt₂
  have ht₁t₂ : t₁ ≠ t₂ := fun h => hm₁ h.symm
  set S : Finset H := {1, u, t, t₁, t₂} with hS
  have hcard : S.card = 5 := by
    rw [hS, Finset.card_insert_of_notMem (by simp [h01, h0t, h0t₁, h0t₂]),
      Finset.card_insert_of_notMem (by simp [hut, hut₁, hut₂]),
      Finset.card_insert_of_notMem (by simp [htt₁, htt₂]),
      Finset.card_insert_of_notMem (by simp [ht₁t₂]), Finset.card_singleton]
  have hsub : (↑S : Set H) ⊆ (T : Set H) := by
    intro x hx
    simp only [hS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact T.one_mem
    · exact hUT huU
    · exact htT
    · rw [ht₁, hκa]
      exact hbT t htT
    · rw [ht₂, hκa, ht₁, hκa]
      exact hbT _ (hbT t htT)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard] at h1
  rw [← Nat.card_coe_set_eq] at h1
  exact h1

theorem eight_le_card_of_isPGroup {T : Subgroup H} (hT : IsPGroup 2 T) (h5 : 5 ≤ Nat.card T) :
    8 ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT
  rw [hk] at h5 ⊢
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · interval_cases k <;> simp at h5
  · calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3

theorem conj_mem_sup {M : Type*} [Group M] {H₁ H₂ : Subgroup M} {g : M}
    (h₁ : ∀ x ∈ H₁, g * x * g⁻¹ ∈ H₁) (h₂ : ∀ x ∈ H₂, g * x * g⁻¹ ∈ H₂) :
    ∀ x ∈ H₁ ⊔ H₂, g * x * g⁻¹ ∈ H₁ ⊔ H₂ := by
  have hle : H₁ ⊔ H₂ ≤ (H₁ ⊔ H₂).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_sup_left (h₁ x hx)
    · exact Subgroup.mem_sup_right (h₂ x hx)
  exact fun x hx => hle hx

end Count

section Bar

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def barAct (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (lBar L) :=
  (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom

@[expose] noncomputable def barImage (L X : Subgroup G) : Subgroup (MulAut (lBar L)) :=
  (X.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAct L)

theorem mem_barImage_iff {L X : Subgroup G} {τ : MulAut (lBar L)} :
    τ ∈ barImage L X ↔ ∃ (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)), g ∈ X ∧
      barAct L ⟨g, hg⟩ = τ := by
  constructor
  · rintro ⟨⟨g, hg⟩, hgX, rfl⟩
    exact ⟨g, hg, Subgroup.mem_subgroupOf.mp hgX, rfl⟩
  · rintro ⟨g, hg, hgX, rfl⟩
    exact ⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.mpr hgX, rfl⟩

theorem commutator_mem_of_barAct_eq_one {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (h : barAct L ⟨g, hg⟩ = 1) {l : G} (hl : l ∈ L) :
    ⁅l, g⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have hgC : g ∈ Sec4.thetaQuotCentralizer L := ⟨⟨g, hg⟩, h, rfl⟩
  obtain ⟨-, hgl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hgC
  have h1 := hgl l⁻¹ (L.inv_mem hl)
  rw [inv_inv] at h1
  rw [commutatorElement_def]
  simpa [mul_assoc] using h1

theorem barImage_ne_bot {L X : Subgroup G} (hXN : X ≤ Subgroup.normalizer (L : Set G))
    (hLX : ⁅L, X⁆ = L) (hq : IsQuasisimple (lBar L)) : barImage L X ≠ ⊥ := by
  intro hbot
  have hle : ⁅L, X⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    rw [Subgroup.commutator_le]
    intro l hl x hx
    have h1 : barAct L ⟨x, hXN hx⟩ = 1 := by
      have hmem : barAct L ⟨x, hXN hx⟩ ∈ barImage L X := mem_barImage_iff.mpr ⟨x, hXN hx, hx, rfl⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact commutator_mem_of_barAct_eq_one (hXN hx) h1 hl
  rw [hLX] at hle
  have hsub : ∀ q : lBar L, q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [QuotientGroup.eq_one_iff]
      obtain ⟨l', hl', hll'⟩ := hle l.2
      have : l' = l := Subtype.ext hll'
      rw [← this]
      exact hl'
  obtain ⟨-, -, a, b, hab⟩ := hq
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a' =>
    induction b using QuotientGroup.induction_on with
    | H b' => rw [hsub a', hsub b']

theorem barImage_commutator {L X Y : Subgroup G} (hX : X ≤ Subgroup.normalizer (L : Set G))
    (hY : Y ≤ Subgroup.normalizer (L : Set G)) :
    barImage L ⁅X, Y⁆ = ⁅barImage L X, barImage L Y⁆ := by
  set N := Subgroup.normalizer (L : Set G) with hN
  have hXY : ⁅X, Y⁆ ≤ N := Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem (hX hx) (hY hy)) (N.inv_mem (hX hx))) (N.inv_mem (hY hy))
  have key : ⁅X, Y⁆.subgroupOf N = ⁅X.subgroupOf N, Y.subgroupOf N⁆ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX,
      Subgroup.map_subgroupOf_eq_of_le hY, Subgroup.map_subgroupOf_eq_of_le hXY]
  rw [barImage, barImage, barImage, key, Subgroup.map_commutator]

theorem barImage_commute {L X Y : Subgroup G} (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    ∀ a ∈ barImage L X, ∀ b ∈ barImage L Y, a * b = b * a := by
  intro a ha b hb
  obtain ⟨x, hxN, hxX, rfl⟩ := mem_barImage_iff.mp ha
  obtain ⟨y, hyN, hyY, rfl⟩ := mem_barImage_iff.mp hb
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hXY x hxX y hyY)

theorem barImage_conj_mem {L X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hgX : ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    ∀ a ∈ barImage L X, barAct L ⟨g, hg⟩ * a * (barAct L ⟨g, hg⟩)⁻¹ ∈ barImage L X := by
  intro a ha
  obtain ⟨x, hxN, hxX, rfl⟩ := mem_barImage_iff.mp ha
  set N := Subgroup.normalizer (L : Set G) with hN
  have hgx : g * x * g⁻¹ ∈ N := N.mul_mem (N.mul_mem hg hxN) (N.inv_mem hg)
  refine mem_barImage_iff.mpr ⟨g * x * g⁻¹, hgx, hgX x hxX, ?_⟩
  have e : (⟨g * x * g⁻¹, hgx⟩ : N) = ⟨g, hg⟩ * ⟨x, hxN⟩ * (⟨g, hg⟩ : N)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]

theorem isPGroup_barImage {p : ℕ} {L X : Subgroup G} (hX : IsPGroup p X) :
    IsPGroup p (barImage L X) :=
  (hX.comap_subtype).map (barAct L)

theorem isElemAbelian_barImage {p : ℕ} {L X : Subgroup G} (hX : IsElemAbelian p X) :
    IsElemAbelian p (barImage L X) := by
  refine Sec4.Item462Proof.isElemAbelian_map' (barAct L) ?_
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
  · have h := hX.1.is_comm.comm (⟨((a : Subgroup.normalizer (L : Set G)) : G), a.2⟩ : X)
      ⟨((b : Subgroup.normalizer (L : Set G)) : G), b.2⟩
    have h' := congrArg Subtype.val h
    exact h'
  · simpa using hX.2 _ (Subgroup.mem_subgroupOf.mp ha)

theorem card_barImage_mul {L X : Subgroup G} (hX : X ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (barImage L X) * Nat.card (X ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) =
      Nat.card X := by
  set N := Subgroup.normalizer (L : Set G) with hN
  have h := Sec4.Config423.card_map_mul_card_inf_ker (barAct L) (X.subgroupOf N)
  have hmap : ((X.subgroupOf N) ⊓ (barAct L).ker).map N.subtype =
      X ⊓ Sec4.thetaQuotCentralizer L := by
    rw [Subgroup.map_inf_eq _ _ N.subtype N.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hX]
    rfl
  have h1 : Nat.card (X ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) =
      Nat.card ((X.subgroupOf N) ⊓ (barAct L).ker : Subgroup N) := by
    rw [← hmap, Subgroup.card_map_of_injective N.subtype_injective]
  have h2 : Nat.card X = Nat.card (X.subgroupOf N) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv).symm
  rw [h1, h2]
  exact h

end Bar

section Star

variable {G : Type} [Group G] [Finite G]

theorem exists_twoGroup_image (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) :
    ∃ T D : Subgroup (MulAut (lBar L)), IsPGroup 2 T ∧ 8 ≤ Nat.card T ∧ IsElemAbelian 3 D ∧
      Nat.card D = 9 ∧ D ≤ Subgroup.normalizer (T : Set (MulAut (lBar L))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hcE, hcU⟩, hc1, hLs, hUN, hVN, hUL, hVL⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hEA : E ≤ A := hpair.mem_E.2
  have hEe : IsElemAbelian 3 E := hpair.mem_E.1.1
  have hE27 : Nat.card E = 27 := hpair.mem_E.1.2.1
  have hcA : c ∈ A := hEA hcE
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hLs
  have hG := hpair.standing.toTheoremFourHyp
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hcA hc1 L hLc
  have hEL : E ≤ Subgroup.normalizer (L : Set G) := hEA.trans hAL
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  obtain ⟨hEU, -, hU4⟩ := mem_fourGroups_iff.mp hpair.mem_U
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set C' := Subgroup.centralizer ((U : Set G) ∪ {c}) with hC'
  set X0 := inSubgroup (CFSG.pCore 2) C' with hX0
  set B := E ⊓ Subgroup.centralizer (U : Set G) with hB
  set V := lThreeV E U c with hV
  have hVX0B : V = ⁅X0, B⁆ := rfl
  have hBC' : B ≤ C' := by
    intro b hb
    rw [hC', Subgroup.mem_centralizer_iff]
    rintro x (hx | hx)
    · exact (Subgroup.mem_centralizer_iff.mp hb.2) x hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hEcomm c hcE b hb.1
  have hBX0 : B ≤ Subgroup.normalizer (X0 : Set G) :=
    hBC'.trans (CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 C')
  have hX02 : IsPGroup 2 X0 := (CFSG.pCore_isPGroup).map C'.subtype
  have hB3 : IsPGroup 3 B := fun g =>
    ⟨1, Subtype.ext (by simpa using hEe.2 _ (Subgroup.mem_inf.mp g.2).1)⟩
  have hX03 : ¬ 3 ∣ Nat.card X0 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX02
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hVB : ⁅V, B⁆ = V := by
    rw [hVX0B]
    exact CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
      Nat.prime_three B X0 hB3 hX03 hBX0
  have hVX0 : V ≤ X0 := by
    rw [hVX0B, Subgroup.commutator_le]
    intro x hx b hb
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine X0.mul_mem hx ?_
    have h1 : b * x⁻¹ * b⁻¹ ∈ X0 :=
      (Subgroup.mem_normalizer_iff.mp (hBX0 hb) x⁻¹).mp (X0.inv_mem hx)
    rwa [mul_assoc] at h1
  have hVU : ∀ v ∈ V, ∀ u ∈ U, v * u = u * v := by
    intro v hv u hu
    have hvC : (v : G) ∈ C' := (Subgroup.map_subtype_le _) (hVX0 hv)
    exact ((Subgroup.mem_centralizer_iff.mp hvC) u (Or.inl hu)).symm
  have hV2 : IsPGroup 2 V := hX02.to_le hVX0
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  have hEUc : ∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U := fun e he u hu =>
    (Subgroup.mem_normalizer_iff.mp (hEU he) u).mp hu
  have hEVc : ∀ e ∈ E, ∀ v ∈ V, e * v * e⁻¹ ∈ V := by
    intro e he v hv
    have hmap := map_lThreeV (MulAut.conj e) E U c
    rw [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer he),
      map_conj_eq_of_mem_normalizer (hEU he)] at hmap
    have hce : (MulAut.conj e) c = c := by
      rw [MulAut.conj_apply, hEcomm e he c hcE, mul_inv_cancel_right]
    rw [hce, ← hV] at hmap
    rw [← hmap]
    exact ⟨v, hv, rfl⟩
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := inf_le_left.trans hEL
  set Uα := barImage L U with hUα
  set Vα := barImage L V with hVα
  set Bα := barImage L B with hBα
  set Eα := barImage L E with hEα
  have hUa : Uα ≠ ⊥ := barImage_ne_bot hUN hUL hq
  have hVa : Vα ≠ ⊥ := barImage_ne_bot hVN hVL hq
  have hVBa : ⁅Vα, Bα⁆ = Vα := by rw [hVα, hBα, ← barImage_commutator hVN hBN, hVB]
  have hUBa : ∀ a ∈ Uα, ∀ b ∈ Bα, a * b = b * a :=
    barImage_commute fun u hu b hb => Subgroup.mem_centralizer_iff.mp hb.2 u hu
  have hUVa : ∀ a ∈ Uα, ∀ b ∈ Vα, a * b = b * a :=
    barImage_commute fun u hu v hv => (hVU v hv u hu).symm
  set T := Uα ⊔ Vα with hT
  have hUa2 : IsPGroup 2 Uα := isPGroup_barImage hU2
  have hVa2 : IsPGroup 2 Vα := isPGroup_barImage hV2
  have hUVn : Uα ≤ Subgroup.normalizer (Vα : Set (MulAut (lBar L))) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hUVa a ha v hv).symm
  have hT2 : IsPGroup 2 T := IsPGroup.to_sup_of_normal_right' hUa2 hVa2 hUVn
  have hET : ∀ e ∈ E, ∀ he : e ∈ Subgroup.normalizer (L : Set G),
      ∀ x ∈ T, barAct L ⟨e, he⟩ * x * (barAct L ⟨e, he⟩)⁻¹ ∈ T := fun e heE he =>
    conj_mem_sup (barImage_conj_mem he (hEUc e heE)) (barImage_conj_mem he (hEVc e heE))
  have hex : ∃ b ∈ Bα, ∃ t ∈ T, b * t * b⁻¹ ≠ t := by
    by_contra hcon
    push Not at hcon
    apply hVa
    rw [← hVBa, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 := hcon b hb v (Subgroup.mem_sup_right hv)
    calc b * v = b * v * b⁻¹ * b := by group
      _ = v * b := by rw [h1]
  obtain ⟨b, hb, t, htT, hbt⟩ := hex
  obtain ⟨g, hgN, hgB, rfl⟩ := mem_barImage_iff.mp hb
  have hg3 : barAct L ⟨g, hgN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨g, hgN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hEe.2 g hgB.1)
    rw [this, map_one]
  have h5 := five_le_card_of_not_commute hg3 (hET g hgB.1 hgN) le_sup_left
    (fun u hu => by rw [← hUBa u hu _ hb, mul_inv_cancel_right]) hUa htT hbt
  refine ⟨T, Eα, hT2, eight_le_card_of_isPGroup hT2 h5, isElemAbelian_barImage hEe, ?_, ?_⟩
  ·
    have hsc := Item211Proof.sectionCentralizer_eq h45 h66 hpair
    rw [Sec13.sectionCentralizer_eq_inf hAL] at hsc
    have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := SetLike.coe_injective hsc
    have hcC : c ∈ Sec4.thetaQuotCentralizer L := by
      have : c ∈ A ⊓ Sec4.thetaQuotCentralizer L := by
        rw [hCA]
        exact Subgroup.mem_zpowers c
      exact this.2
    have hEC : E ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
      refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨hcE, hcC⟩)
      rw [← hCA]
      exact inf_le_inf_right _ hEA
    have hc3 : orderOf c = 3 := orderOf_eq_prime (hEe.2 c hcE) hc1
    have h : Nat.card Eα * Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) =
        Nat.card E := card_barImage_mul hEL
    rw [hEC, Nat.card_zpowers, hc3, hE27] at h
    omega
  · intro d hd
    obtain ⟨e, heN, heE, rfl⟩ := mem_barImage_iff.mp hd
    exact Subgroup.mem_normalizer_fintype (hET e heE heN)

end Star

@[expose] def TwoLocalSmallIn (M : Type) [Group M] : Prop :=
  ∀ T D : Subgroup M, IsPGroup 2 T → IsElemAbelian 3 D → Nat.card D = 9 →
    D ≤ Subgroup.normalizer (T : Set M) → Nat.card T ≤ 4

@[expose] def TwoLocalSmall (X : Type) [Group X] : Prop :=
  TwoLocalSmallIn (MulAut X)

theorem TwoLocalSmallIn.of_injective {M N : Type} [Group M] [Group N] (hN : TwoLocalSmallIn N)
    (φ : M →* N) (hφ : Function.Injective φ) : TwoLocalSmallIn M := by
  intro T D hT hD hD9 hDT
  have hDT' : D.map φ ≤ Subgroup.normalizer ((T.map φ : Subgroup N) : Set N) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨d * t * d⁻¹, (Subgroup.mem_normalizer_iff.mp (hDT hd) t).mp ht, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · rintro ⟨t, ht, hx⟩
      refine ⟨d⁻¹ * t * d, ?_, ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.mp (hDT (D.inv_mem hd)) t).mp ht
        rwa [inv_inv] at h1
      · rw [map_mul, map_mul, map_inv, hx]
        group
  have h := hN (T.map φ) (D.map φ) (hT.map φ) (Sec4.Item462Proof.isElemAbelian_map' φ hD)
    (by rw [Subgroup.card_map_of_injective hφ, hD9]) hDT'
  rwa [Subgroup.card_map_of_injective hφ] at h

theorem TwoLocalSmall.of_mulEquiv {X Y : Type} [Group X] [Group Y] (hY : TwoLocalSmall Y)
    (e : X ≃* Y) : TwoLocalSmall X :=
  TwoLocalSmallIn.of_injective hY (MulAut.congr e).toMonoidHom (MulAut.congr e).injective

theorem twoLocalSmall_of_center_quotient {X : Type} [Group X] [Group.IsPerfect X]
    (h : TwoLocalSmall (X ⧸ Subgroup.center X)) : TwoLocalSmall X := by
  refine TwoLocalSmallIn.of_injective h (KFacts.centerDescend X) ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  rw [Subgroup.mem_bot]
  refine KFacts.eq_one_of_forall_mul_inv_mem_center fun s => ?_
  have h1 := congrArg (fun φ : MulAut (X ⧸ Subgroup.center X) =>
    φ (s : X ⧸ Subgroup.center X)) hσ
  simp only [KFacts.centerDescend_mk, MulAut.one_apply] at h1
  rw [QuotientGroup.eq] at h1
  have := (Subgroup.center X).inv_mem h1
  simpa using this

theorem twoLocalSmall_alternatingGroup_seven (h : TwoLocalSmallIn (Equiv.Perm (Fin 7))) :
    TwoLocalSmall (alternatingGroup (Fin 7)) := by
  have hc := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  set e := MulEquiv.ofBijective _ hc with he
  exact TwoLocalSmallIn.of_injective h e.symm.toMonoidHom e.symm.injective

end Item211Res2Proof

open Item211Res2Proof

@[expose] def KS211TwoLocalM12 : Prop :=
  TwoLocalSmall NativeSporadic.M12

@[expose] def KS211TwoLocalS7 : Prop :=
  TwoLocalSmallIn (Equiv.Perm (Fin 7))

theorem ks211TwoLocalSmall_of (hM : KS211TwoLocalM12) (hS : KS211TwoLocalS7) :
    TwoLocalSmall NativeSporadic.M12 ∧ TwoLocalSmall (alternatingGroup (Fin 7)) ∧
      ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
        Sec4.IsTripleCover X (alternatingGroup (Fin 7)) → TwoLocalSmall X := by
  refine ⟨hM, twoLocalSmall_alternatingGroup_seven hS, fun X _ _ hq hT => ?_⟩
  obtain ⟨-, ⟨e⟩⟩ := hT
  have : Group.IsPerfect X := hq.1
  exact twoLocalSmall_of_center_quotient ((twoLocalSmall_alternatingGroup_seven hS).of_mulEquiv e)

section Certs


@[expose] def Item211ResidualON : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
    (∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField) →
    Nat.card A = 3 ^ 3 → Sec4.IsTripleCover (lBar L) NativeSporadic.ON → False

theorem item211ResidualSmall_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hM : KS211TwoLocalM12) (hS : KS211TwoLocalS7) (hON : Item211ResidualON) :
    Item211ResidualSmall := by
  have hK := ks211TwoLocalSmall_of hM hS
  intro G _ _ A E U c L hpair hnf hcase
  obtain ⟨T, D, hT2, hT8, hDe, hD9, hDT⟩ := exists_twoGroup_image h45 h66 hpair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  rcases hcase with ⟨-, -, hT⟩ | ⟨-, he, -⟩ | ⟨-, he, -⟩ | ⟨h27, h8⟩
  · have := hK.2.2 (lBar L) hq hT T D hT2 hDe hD9 hDT
    omega
  · obtain ⟨e⟩ := he
    have := (hK.2.1.of_mulEquiv e) T D hT2 hDe hD9 hDT
    omega
  · obtain ⟨e⟩ := he
    have := (hK.1.of_mulEquiv e) T D hT2 hDe hD9 hDT
    omega
  · exact hON G A E U c L hpair hnf h27 h8

end Certs

end CFSG.RankThree.PartTwo.Sec21
