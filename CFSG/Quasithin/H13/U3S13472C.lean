module

public import CFSG.Quasithin.H13.U3S13472B
public import CFSG.Quasithin.Vol2.Ch1A3Cat

public section

namespace CFSG.Quasithin.H13.U3.P2

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
variable {S : A6.Setting134 G T L V} {H₁ H₂ : Subgroup G}

structure SettingX (D : Data2 S H₁ H₂) (X : Subgroup G) : Prop where
  hX : InH (H₁ ⊔ H₂) X
  hXZ : X ⊓ centralizer (quasithinOmegaOneCenter T : Set G) = T
  hK₀X : D.K₀ ∈ cComp X
  hNX : X ≤ normalizer (D.K₀ : Set G)

theorem settingX_of (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h1345 : NQS134.Stmt13_4_5)
    (D : Data2 S H₁ H₂) {X : Subgroup G} (hX : InH (H₁ ⊔ H₂) X)
    (hXZ : X ⊓ centralizer (quasithinOmegaOneCenter T : Set G) = T) : SettingX D X := by
  have hTX : T ≤ X := D.hH₀.1.trans hX.1
  have hXT : InH T X := ⟨hTX, hX.2⟩
  have hsylX : IsSylowTwoOf T X := A5.isSylowTwoOf_of_le S.h13.sylow hTX
  have hXM : ¬ X ≤ normalizer (L : Set G) := fun h => D.hH₀M (hX.1.trans h)
  have hns : ¬ Group.IsSolvable ↥X := fun hs => s1347_not_solvable_of_cComp D.hK₀
    (Group.isSolvable_of_isSolvable_injective (inclusion_injective hX.1))
  obtain ⟨-, hall⟩ := h1345 G T L V S X hXT hXM hns
  have hKX : D.K₀ ≤ X := D.KH.trans hX.1
  have hKl : D.K₀ ∈ lFamily T := D.hmax.1.2.1
  obtain ⟨K, hK, hKK⟩ := lemma_1_2_4_exists S.h13.qtke S.h13.simple S.h13.nonabelian
    (a37ForSQTK_of_cat h37) (a39ForSQTK_of_cat h39) hX.2 hsylX hKX hKl
  obtain ⟨⟨hKmax, -⟩, hN, -⟩ := hall K hK
  have hKeq : K = D.K₀ := D.hmax.2 K hKmax.1 hKK
  subst hKeq
  exact ⟨hX, hXZ, hK, hN⟩

namespace SettingX

variable {D : Data2 S H₁ H₂} {X : Subgroup G}

theorem TX (hS : SettingX D X) : T ≤ X := D.hH₀.1.trans hS.hX.1

theorem sylow (hS : SettingX D X) : IsSylowTwoOf T X := A5.isSylowTwoOf_of_le S.h13.sylow hS.TX

theorem inH (hS : SettingX D X) : InH T X := ⟨hS.TX, hS.hX.2⟩

theorem KX (hS : SettingX D X) : D.K₀ ≤ X := D.KH.trans hS.hX.1

theorem reduced (hS : SettingX D X) :
    IsTwoReducedIn X (conjClosure (quasithinOmegaOneCenter T) X) :=
  C1GN.isTwoReducedIn_VZ (s134_charTwo_of_inH S hS.inH) hS.sylow

theorem V0_le (hS : SettingX D X) :
    v0Of T H₁ H₂ ≤ conjClosure (quasithinOmegaOneCenter T) X :=
  conjClosure_mono le_rfl hS.hX.1

theorem pCoreOf_le_centralizer (hS : SettingX D X) :
    pCoreOf 2 X ≤ centralizer (conjClosure (quasithinOmegaOneCenter T) X : Set G) :=
  pCoreOf_le_centralizer_of_reduced' hS.reduced

theorem le_T (hS : SettingX D X) : conjClosure (quasithinOmegaOneCenter T) X ≤ T := by
  have hred := hS.reduced
  refine (QuasithinUnique.le_pCoreOf_of_le_normalizer hred.1 hred.2.1 ?_).trans
    (pCoreOf_two_le_of_isSylowTwoOf hS.sylow)
  rintro ⟨w, hw⟩
  exact ⟨1, Subtype.ext (by simpa using hred.2.2.1.2 w hw)⟩

theorem inf_centralizer_le_T (hS : SettingX D X) :
    X ⊓ centralizer (conjClosure (quasithinOmegaOneCenter T) X : Set G) ≤ T := by
  exact (inf_le_inf_left _ (Subgroup.centralizer_le (le_conjClosure _ _))).trans hS.hXZ.le

end SettingX

theorem exists_A (D : Data2 S H₁ H₂) (hJ1 : ⁅oTwoRes H₂, thompsonJi T 1⁆ = oTwoRes H₂) :
    ∃ A : Subgroup G, IsElemAbelianCorank T 1 A ∧
      ¬ A ≤ centralizer (v0Of T H₁ H₂ : Set G) := by
  by_contra hcon
  push Not at hcon
  have hJ : thompsonJi T 1 ≤ pCoreOf 2 (H₁ ⊔ H₂) := by
    rw [← s1347_T_inf_centralizer S D.hyp D.hH₀]
    exact iSup₂_le fun A hA => le_inf hA.1 (hcon A hA)
  have hK₂H : oTwoRes H₂ ≤ H₁ ⊔ H₂ := (oTwoRes_le H₂).trans le_sup_right
  have hK₂ : oTwoRes H₂ ≤ pCoreOf 2 (H₁ ⊔ H₂) := by
    rw [← hJ1, commutator_le]
    intro k hk j hj
    have hkH := hK₂H hk
    have hj' := hJ hj
    have h1 := (mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (H₁ ⊔ H₂) hkH) j).1 hj'
    exact mul_mem h1 (inv_mem hj')
  apply s1347_not_le_centralizer_Z S D.hyp.inH₂.1 D.hyp.index₂
  refine hK₂.trans (le_trans ?_ (Subgroup.centralizer_le (s1347_Z_le_V0 (H₁ := H₁) (H₂ := H₂))))
  rw [← D.hcent]
  exact inf_le_right

theorem eq_of_lt_of_le_two {a b c : ℕ} (ha : ∃ i, a = 2 ^ i) (hb : ∃ j, b = 2 ^ j)
    (hc : ∃ n, c = 2 ^ n) (hlt : a * b < c) (hle : c ≤ a * b * 2 ^ 1) : c = a * b * 2 ^ 1 := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨n, rfl⟩ := hc
  rw [← pow_add, ← pow_add] at *
  have h1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hlt
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
  rw [show n = i + j + 1 by omega]

theorem card_eq_two_pow_of_le {P Q : Subgroup G} (hP : IsPGroup 2 P) (hQP : Q ≤ P) :
    ∃ n, Nat.card Q = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (hP.to_le hQP).exists_card_eq

theorem relIndex_eq_two_pow {A B : Subgroup G} (hA : IsPGroup 2 A) :
    ∃ n, B.relIndex A = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hA.exists_card_eq
  have hd : B.relIndex A ∣ 2 ^ m := hm ▸ Subgroup.relIndex_dvd_card B A
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact ⟨n, hn⟩

theorem card_V0_eq (D : Data2 S H₁ H₂) {A : Subgroup G} (hA : IsElemAbelianCorank T 1 A)
    (hAC : ¬ A ≤ centralizer (v0Of T H₁ H₂ : Set G)) :
    Nat.card ↥(v0Of T H₁ H₂) = (A ⊓ centralizer (v0Of T H₁ H₂ : Set G)).relIndex A *
      Nat.card ↥(v0Of T H₁ H₂ ⊓ centralizer (A : Set G)) * 2 ^ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV0e : IsElemAbelian 2 (v0Of T H₁ H₂) := D.reduced.2.2.1
  have hV0T : v0Of T H₁ H₂ ≤ T := s1347_V0_le_T S D.hH₀
  have hV0p : IsPGroup 2 ↥(v0Of T H₁ H₂) := (S.h13.sylow.1).to_le hV0T
  have hAp : IsPGroup 2 ↥A := (S.h13.sylow.1).to_le hA.1
  exact eq_of_lt_of_le_two (relIndex_eq_two_pow hAp) (card_eq_two_pow_of_le hV0p inf_le_left)
    hV0p.exists_card_eq (D.noFF hA.1 hA.2.1 hAC)
    (card_le_relIndex_mul_card_mul_two_pow hV0e hV0T hA)

theorem isMaxElemAbelian_B (D : Data2 S H₁ H₂) {A : Subgroup G}
    (hA : IsElemAbelianCorank T 1 A) (hAC : ¬ A ≤ centralizer (v0Of T H₁ H₂ : Set G)) :
    IsMaxElemAbelian T ((A ⊓ centralizer (v0Of T H₁ H₂ : Set G)) ⊔ v0Of T H₁ H₂) :=
  isMaxElemAbelian_sup_of_eq D.reduced.2.2.1 (s1347_V0_le_T S D.hH₀) hA (card_V0_eq D hA hAC)

omit [Finite G] in
theorem conj_mem_commutator {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) {c : G} (hc : c ∈ ⁅A, B⁆) : g * c * g⁻¹ ∈ ⁅A, B⁆ := by
  rw [Subgroup.commutator_def] at hc
  induction hc using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hw
    have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact commutator_mem_commutator ((mem_normalizer_iff.1 hA a).1 ha)
      ((mem_normalizer_iff.1 hB b).1 hb)
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul a b _ _ ha hb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

@[expose] def centQuot (V₀ W : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ normalizer (V₀ : Set G) ∧ g ∈ normalizer (W : Set G) ∧
    ∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ V₀}
  one_mem' := ⟨one_mem _, one_mem _, fun w _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact one_mem _⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, mul_mem ha.2.1 hb.2.1, fun w hw => by
    have h1 := (mem_normalizer_iff.1 ha.1 _).1 (hb.2.2 w hw)
    have e : a * b * w * (a * b)⁻¹ * w⁻¹ =
        a * (b * w * b⁻¹ * w⁻¹) * a⁻¹ * (a * w * a⁻¹ * w⁻¹) := by group
    rw [e]
    exact mul_mem h1 (ha.2.2 w hw)⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, inv_mem ha.2.1, fun w hw => by
    have hw' : a⁻¹ * w * a ∈ W := by
      have := (mem_normalizer_iff.1 (inv_mem ha.2.1) w).1 hw
      simpa using this
    have h1 := ha.2.2 _ hw'
    have e : a⁻¹ * w * a⁻¹⁻¹ * w⁻¹ = (a * (a⁻¹ * w * a) * a⁻¹ * (a⁻¹ * w * a)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1⟩

omit [Finite G] in
theorem conj_mem_centQuot {V₀ W : Subgroup G} {k : G} (hkV : k ∈ normalizer (V₀ : Set G))
    (hkW : k ∈ normalizer (W : Set G)) {g : G} (hg : g ∈ centQuot V₀ W) :
    k * g * k⁻¹ ∈ centQuot V₀ W := by
  refine ⟨mul_mem (mul_mem hkV hg.1) (inv_mem hkV), mul_mem (mul_mem hkW hg.2.1) (inv_mem hkW),
    fun w hw => ?_⟩
  have hw' : k⁻¹ * w * k ∈ W := by
    have := (mem_normalizer_iff.1 (inv_mem hkW) w).1 hw
    simpa using this
  have h1 := (mem_normalizer_iff.1 hkV _).1 (hg.2.2 _ hw')
  have e : k * g * k⁻¹ * w * (k * g * k⁻¹)⁻¹ * w⁻¹ =
      k * (g * (k⁻¹ * w * k) * g⁻¹ * (k⁻¹ * w * k)⁻¹) * k⁻¹ := by group
  rw [e]
  exact h1

theorem eq_V0_of_B (D : Data2 S H₁ H₂) {X : Subgroup G} (hS : SettingX D X) {A : Subgroup G}
    (hA : IsElemAbelianCorank T 1 A) (hAC : ¬ A ≤ centralizer (v0Of T H₁ H₂ : Set G))
    (hB : (A ⊓ centralizer (v0Of T H₁ H₂ : Set G)) ⊔ v0Of T H₁ H₂ ≤
      centralizer (conjClosure (quasithinOmegaOneCenter T) X : Set G)) :
    conjClosure (quasithinOmegaOneCenter T) X = v0Of T H₁ H₂ := by
  set W := conjClosure (quasithinOmegaOneCenter T) X with hWdef
  set V₀ := v0Of T H₁ H₂ with hV₀def
  have hred := hS.reduced
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have hWT : W ≤ T := hS.le_T
  have hV0W : V₀ ≤ W := hS.V0_le
  have hCA : A ⊓ centralizer (W : Set G) = A ⊓ centralizer (V₀ : Set G) :=
    le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le hV0W))
      (le_inf inf_le_left (le_sup_left.trans hB))
  have heq0 := card_V0_eq D hA hAC
  have hW := card_le_relIndex_mul_card_mul_two_pow hWe hWT hA
  rw [hCA] at hW
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hWe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcomm : ∀ a ∈ V₀, ∀ b ∈ W ⊓ centralizer (A : Set G), a * b = b * a := fun a ha b hb =>
    hWc a (hV0W ha) b hb.1
  have hcard := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf : V₀ ⊓ (W ⊓ centralizer (A : Set G)) = V₀ ⊓ centralizer (A : Set G) := by
    rw [← inf_assoc, inf_eq_left.2 hV0W]
  rw [hinf, heq0] at hcard
  have hpos : 0 < Nat.card ↥(V₀ ⊓ centralizer (A : Set G)) := Nat.card_pos
  have hge : Nat.card W ≤ Nat.card ↥(V₀ ⊔ W ⊓ centralizer (A : Set G)) := by
    refine hW.trans (Nat.le_of_mul_le_mul_right ?_ hpos)
    rw [hcard]
    apply le_of_eq
    ring
  have hWeq : V₀ ⊔ W ⊓ centralizer (A : Set G) = W :=
    Subgroup.eq_of_le_of_card_ge (sup_le hV0W inf_le_left) hge
  have hAV : A ≤ normalizer (V₀ : Set G) := hA.1.trans (D.hH₀.1.trans D.reduced.2.1)
  have hWA : ∀ a ∈ A, ∀ w ∈ W, a * w * a⁻¹ * w⁻¹ ∈ V₀ := by
    intro a ha w hw
    have hCn : W ⊓ centralizer (A : Set G) ≤ normalizer (V₀ : Set G) := fun c hc =>
      centralizer_le_normalizer _ (mem_centralizer_iff.2 fun v hv => hWc v (hV0W hv) c hc.1)
    rw [← hWeq] at hw
    obtain ⟨v, hv, c, hc, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hCn hw
    have hac : a * c = c * a := (mem_centralizer_iff.1 hc.2 a ha)
    have hca : c * a⁻¹ = a⁻¹ * c := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hac, ← mul_assoc, inv_mul_cancel, one_mul]
    have e : a * (v * c) * a⁻¹ * (v * c)⁻¹ = a * v * a⁻¹ * v⁻¹ := by
      calc a * (v * c) * a⁻¹ * (v * c)⁻¹ = a * v * (c * a⁻¹) * c⁻¹ * v⁻¹ := by group
        _ = a * v * (a⁻¹ * c) * c⁻¹ * v⁻¹ := by rw [hca]
        _ = a * v * a⁻¹ * v⁻¹ := by group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.1 (hAV ha) v).1 hv) (inv_mem hv)
  have hO : pCoreOf 2 (H₁ ⊔ H₂) ≤ centralizer (V₀ : Set G) := D.hcent ▸ inf_le_right
  obtain ⟨a, ha, haO⟩ : ∃ a ∈ A, a ∉ pCoreOf 2 (H₁ ⊔ H₂) := by
    by_contra hcon
    push Not at hcon
    exact hAC fun a ha => hO (hcon a ha)
  have haH : a ∈ H₁ ⊔ H₂ := D.hH₀.1 (hA.1 ha)
  obtain ⟨k, hk, hkO⟩ : ∃ k ∈ D.K₀, a * k * a⁻¹ * k⁻¹ ∉ pCoreOf 2 (H₁ ⊔ H₂) := by
    by_contra hcon
    push Not at hcon
    exact haO (D.mem_pCoreOf_of_comm haH hcon)
  have hKV : D.K₀ ≤ normalizer (V₀ : Set G) := D.KH.trans D.reduced.2.1
  have hKW : D.K₀ ≤ normalizer (W : Set G) := hS.KX.trans hred.2.1
  have hcK : a * k * a⁻¹ * k⁻¹ ∈ D.K₀ :=
    mul_mem ((mem_normalizer_iff.1 (D.hN haH) k).1 hk) (inv_mem hk)
  have hcO : a * k * a⁻¹ * k⁻¹ ∉ pCoreOf 2 D.K₀ := fun h =>
    hkO (pCoreOf_le_pCoreOf D.KH D.hN h)
  have haQ : a ∈ centQuot V₀ W :=
    ⟨hAV ha, hS.reduced.2.1 (hS.TX (hA.1 ha)), hWA a ha⟩
  have hcQ : a * k * a⁻¹ * k⁻¹ ∈ centQuot V₀ W := by
    have h1 := conj_mem_centQuot (hKV hk) (hKW hk) (inv_mem haQ)
    have e : a * k * a⁻¹ * k⁻¹ = a * (k * a⁻¹ * k⁻¹) := by group
    rw [e]
    exact mul_mem haQ h1
  have hperf : ⁅D.K₀, D.K₀⁆ = D.K₀ := D.hK₀.2.1
  have hs : IsSimpleGroup (↥D.K₀ ⧸ CFSG.pCore 2 ↥D.K₀) := by
    obtain ⟨e⟩ := (quasithinO2QuotientIso_iff _ _).1 D.hK
    have : IsSimpleGroup SL3.S := HSType.isSimpleGroup_SL_three_two
    exact e.isSimpleGroup
  have hKWV := comm_le_of_simple hperf hs hKW hKV hcK hcO hcQ.2.2
  have hcommle : ⁅D.K₀, W⁆ ≤ V₀ := by
    rw [commutator_le]
    exact fun k hk w hw => hKWV k hk w hw
  have hWle : W ≤ ⁅D.K₀, W⁆ := by
    refine conjClosure_le fun g hg z hz => ?_
    have hz' : z ∈ ⁅D.K₀, W⁆ := commutator_mono le_rfl hV0W (D.Z_le_commutator hz)
    exact conj_mem_commutator (hS.hNX hg) (hred.2.1 hg) hz'
  exact le_antisymm (hWle.trans hcommle) hV0W

end CFSG.Quasithin.H13.U3.P2
