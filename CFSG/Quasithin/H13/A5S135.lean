module

public import CFSG.Quasithin.H13.A5S133
public import CFSG.Quasithin.Background.F9Five

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

@[expose] def c01 : W5 →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (((Multiplicative.toAdd x : ↥Ev) : Fin 5 → ZMod 2) 0 +
    ((Multiplicative.toAdd x : ↥Ev) : Fin 5 → ZMod 2) 1)
  map_one' := rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (_ + _) = Multiplicative.ofAdd (_ + _) * Multiplicative.ofAdd (_ + _)
    rw [← ofAdd_add]
    congr 1
    show (((Multiplicative.toAdd x : ↥Ev) : Fin 5 → ZMod 2) 0 +
        ((Multiplicative.toAdd y : ↥Ev) : Fin 5 → ZMod 2) 0) +
      (((Multiplicative.toAdd x : ↥Ev) : Fin 5 → ZMod 2) 1 +
        ((Multiplicative.toAdd y : ↥Ev) : Fin 5 → ZMod 2) 1) = _
    ring

@[expose] def W2 : Subgroup W5 := W3 ⊓ c01.ker

@[expose] def InW2 (x : W5) : Prop := c4 x = 1 ∧ c01 x = 1

instance : DecidablePred InW2 := fun x => inferInstanceAs (Decidable (c4 x = 1 ∧ c01 x = 1))

theorem mem_W2 {x : W5} : x ∈ W2 ↔ InW2 x :=
  ⟨fun h => ⟨mem_W3.1 h.1, h.2⟩, fun h => ⟨mem_W3.2 h.1, h.2⟩⟩

@[expose] def FixW2 (σ : Equiv.Perm (Fin 5)) : Prop := ∀ x : W5, InW2 x → pact σ x = x

instance : DecidablePred FixW2 := fun σ =>
  inferInstanceAs (Decidable (∀ x : W5, InW2 x → pact σ x = x))

theorem K4_fix_W2 : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → FixW2 σ → σ = 1 ∨ σ = pa := by
  decide +kernel

theorem comm_pa_W2 : ∀ x : W5, InW2 (pact pa x * x⁻¹) := by
  decide +kernel

@[expose] def NS2 (x : W5) : Prop := x ≠ 1 ∧ x ≠ W4 ∧ ¬ IsSing x ∧ ¬ IsSing (x * W4)

instance : DecidablePred NS2 := fun x =>
  inferInstanceAs (Decidable (x ≠ 1 ∧ x ≠ W4 ∧ ¬ IsSing x ∧ ¬ IsSing (x * W4)))

theorem c4_of_NS2 : ∀ x : W5, NS2 x → c4 x = 1 := by
  decide +kernel

theorem NS2_of_W2 : ∀ x : W5, InW2 x → x ≠ 1 → x ≠ W4 → NS2 x := by
  decide +kernel

@[expose] def GenW2 (y : W5) : Prop := ∀ x : W5, InW2 x → x ∈ [1, W4, y, y * W4]

instance : DecidablePred GenW2 := fun y =>
  inferInstanceAs (Decidable (∀ x : W5, InW2 x → x ∈ [1, W4, y, y * W4]))

theorem W2_gen : ∀ y : W5, InW2 y → y ≠ 1 → y ≠ W4 → GenW2 y := by
  decide +kernel

theorem exists_c3p_pow_W2 : ∀ y : W5, c4 y = 1 → y ≠ 1 → y ≠ W4 →
    (c01 y = 1 ∨ c01 (pact c3p y) = 1 ∨ c01 (pact (c3p * c3p) y) = 1) := by
  decide +kernel

theorem c3p_pow_fix4 (k : ℕ) : (c3p ^ k) 4 = 4 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, Equiv.Perm.mul_apply, c3p_four, ih]

@[expose] def Input1336 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V),
    ¬ S.G1 ≤ Subgroup.normalizer (L : Set G)

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

@[expose] noncomputable def V2 : Subgroup G := S.pre W2

theorem V2_le_V3 : S.V2 ≤ S.V3 := S.pre_mono inf_le_left

theorem V1_le_V2 : S.V1 ≤ S.V2 := by
  unfold V1
  rw [Subgroup.zpowers_le]
  refine S.mem_pre.2 ⟨S.z_mem_V, ?_⟩
  rw [S.psi_z]
  exact mem_W2.2 (by decide +kernel)

theorem V1_le_pCoreOf_G1 : S.V1 ≤ pCoreOf 2 S.G1 := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
  · rw [S.G1_eq_normalizer]
    exact Subgroup.le_normalizer
  · rw [S.G1_eq_normalizer]
  · exact (S.isPGroup_V).to_le S.V1_le_V

theorem G1_mem_Hz (h1336 : Input1336) : S.G1 ∈ S.Hz := by
  refine ⟨⟨?_, ?_⟩, le_rfl, h1336 G T L V S⟩
  · rw [S.G1_eq_normalizer]
    exact S.L1T_le_NV1
  · intro h
    have := S.V1_le_pCoreOf_G1
    rw [h, le_bot_iff] at this
    have hc := S.card_V1
    rw [this] at hc
    simp at hc

theorem V3_lt_conjClosure (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz) :
    S.V3 < conjClosure S.V3 H := by
  refine lt_of_le_of_ne (le_conjClosure _ _) fun h => hH.2.2 ?_
  have hN : H ≤ Subgroup.normalizer (S.V3 : Set G) := by
    rw [h]; exact le_normalizer_conjClosure _ _
  exact (hN.trans (h1323 G T L V S)).trans S.NV_le_M

theorem centralizer_V3_inf (H : Subgroup G) :
    (H ⊓ Subgroup.centralizer (S.V3 : Set G)) ⊓ (H ⊓ Subgroup.normalizer (V : Set G)) =
      H ⊓ Subgroup.centralizer (V : Set G) := by
  apply le_antisymm
  · rintro x ⟨⟨hxH, hx3⟩, -, hxN⟩
    exact ⟨hxH, S.mem_centralizer_V_of_V3 hxN hx3⟩
  · rintro x ⟨hxH, hxV⟩
    refine ⟨⟨hxH, Subgroup.centralizer_le (s := (S.V3 : Set G)) (t := (V : Set G))
      (fun y hy => S.V3_le_V hy) hxV⟩, hxH, Subgroup.centralizer_le_normalizer _ hxV⟩

theorem tfae_13_5_10 (h1323 : Input1323Two) {H : Subgroup G} (hH : H ∈ S.Hz) :
    List.TFAE [V ≤ pCoreOf 2 H, IsElemAbelian 2 (conjClosure S.V3 H),
      IsElemAbelian 2 (conjClosure V H)] :=
  (S.hypF91 h1323 hH).F94_3 (S.centralizer_V3_inf H)

theorem conj_mem_V3_of_V2 (h1326 : Input1326Two) {g x : G} (hg : g ∈ S.G1) (hx : x ∈ S.V2)
    (hxV : g * x * g⁻¹ ∈ V) : g * x * g⁻¹ ∈ S.V3 := by
  obtain ⟨hxV', hxW⟩ := S.mem_pre.1 hx
  have hgz : g * S.z * g⁻¹ = S.z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc g * S.z * g⁻¹ = S.z * g * g⁻¹ := by rw [this]
      _ = S.z := by group
  by_cases h1 : S.frame.ψ ⟨x, hxV'⟩ = 1
  · have : (⟨x, hxV'⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [h1, map_one])
    have hx1 : x = 1 := congrArg Subtype.val this
    rw [hx1, mul_one, mul_inv_cancel]
    exact S.V3.one_mem
  by_cases h2 : S.frame.ψ ⟨x, hxV'⟩ = W4
  · have : (⟨x, hxV'⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := S.frame.ψ.injective (by rw [h2, S.psi_z])
    have hxz : x = S.z := congrArg Subtype.val this
    rw [hxz, hgz]
    exact S.z_mem_V3
  obtain ⟨-, -, hns, hns'⟩ := NS2_of_W2 _ (mem_W2.1 hxW) h1 h2
  have hy := (h1326 G T L V S g ⟨x, hxV'⟩ ⟨g * x * g⁻¹, hxV⟩ rfl).not.1 hns
  have hxzV : x * S.z ∈ V := V.mul_mem hxV' S.z_mem_V
  have hyzV : g * x * g⁻¹ * S.z ∈ V := V.mul_mem hxV S.z_mem_V
  have hconj : g * (x * S.z) * g⁻¹ = g * x * g⁻¹ * S.z := by
    calc g * (x * S.z) * g⁻¹ = g * x * g⁻¹ * (g * S.z * g⁻¹) := by group
      _ = g * x * g⁻¹ * S.z := by rw [hgz]
  have hyz := (h1326 G T L V S g ⟨x * S.z, hxzV⟩ ⟨g * x * g⁻¹ * S.z, hyzV⟩
    hconj).not.1 (by
      have : S.frame.ψ ⟨x * S.z, hxzV⟩ = S.frame.ψ ⟨x, hxV'⟩ * W4 := by
        rw [← S.psi_z, ← map_mul]; rfl
      rw [this]; exact hns')
  have hψ : S.frame.ψ ⟨g * x * g⁻¹ * S.z, hyzV⟩ = S.frame.ψ ⟨g * x * g⁻¹, hxV⟩ * W4 := by
    rw [← S.psi_z, ← map_mul]; rfl
  rw [hψ] at hyz
  have hy1 : S.frame.ψ ⟨g * x * g⁻¹, hxV⟩ ≠ 1 := by
    intro h
    apply h1
    have : (⟨g * x * g⁻¹, hxV⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [h, map_one])
    have e := congrArg Subtype.val this
    have hx1 : x = 1 := by
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, show (g * x * g⁻¹) = 1 from e]; group
    have : (⟨x, hxV'⟩ : ↥V) = 1 := Subtype.ext hx1
    rw [this, map_one]
  have hy2 : S.frame.ψ ⟨g * x * g⁻¹, hxV⟩ ≠ W4 := by
    intro h
    apply h2
    have : (⟨g * x * g⁻¹, hxV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ :=
      S.frame.ψ.injective (by rw [h, S.psi_z])
    have e := congrArg Subtype.val this
    have hgz' : g⁻¹ * S.z * g = S.z := by
      calc g⁻¹ * S.z * g = g⁻¹ * (g * S.z * g⁻¹) * g := by rw [hgz]
        _ = S.z := by group
    have hxz : x = S.z := by
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, show (g * x * g⁻¹) = S.z from e, hgz']
    have : (⟨x, hxV'⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := Subtype.ext hxz
    rw [this, S.psi_z]
  exact S.mem_pre.2 ⟨hxV, mem_W3.2 (c4_of_NS2 _ ⟨hy1, hy2, hy, hyz⟩)⟩


theorem V2_le_conj_V3 (h1326 : Input1326Two) {g : G} (hg : g ∈ S.G1)
    (hV2 : S.V2 ≤ conjSub g⁻¹ V) : S.V2 ≤ conjSub g⁻¹ S.V3 := by
  intro x hx
  have hxV : g * x * g⁻¹ ∈ V := by
    have := hV2 hx
    rwa [mem_conjSub, inv_inv] at this
  rw [mem_conjSub, inv_inv]
  exact S.conj_mem_V3_of_V2 h1326 hg hx hxV

theorem le_normalizer_conj_of_V2 (h1323 : Input1323Two) (h1326 : Input1326Two)
    (h1336 : Input1336) {g : G} (hg : g ∈ S.G1) (hV2 : S.V2 ≤ conjSub g⁻¹ V) :
    V ≤ Subgroup.normalizer (conjSub g⁻¹ V : Set G) := by
  have hF := S.hypF91 h1323 (S.G1_mem_Hz h1336)
  have hginv : g⁻¹ ∈ S.G1 := S.G1.inv_mem hg
  have hV3U : conjSub g⁻¹ S.V3 ≤ conjClosure S.V3 S.G1 := HypF91.conjSub_le_conjClosure hginv
  have hUQ : conjClosure S.V3 S.G1 ≤ pCoreOf 2 S.G1 := hF.conjClosure_Vp_le_pCoreOf
  have hQT : pCoreOf 2 S.G1 ≤ T := F7.isSylowTwoOf_pCoreOf_le hF.sylow_H
  have hVg : IsElemAbelian 2 (conjSub g⁻¹ V) := F7.isElemAbelian_conjSub S.elemAbelian_V
  have hbN : ∀ b ∈ conjSub g⁻¹ S.V3, b ∈ Subgroup.normalizer (V : Set G) := fun b hb =>
    S.frame.T_le (hQT (hUQ (hV3U hb)))
  have hbρ : ∀ (b : G) (hb : b ∈ conjSub g⁻¹ S.V3), S.frame.ρ ⟨b, hbN b hb⟩ = 1 ∨
      S.frame.ρ ⟨b, hbN b hb⟩ = pa := by
    intro b hb
    have hbG1 : b ∈ S.G1 := (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (hUQ (hV3U hb))
    have hbz : b * S.z * b⁻¹ = S.z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hbG1
      calc b * S.z * b⁻¹ = S.z * b * b⁻¹ := by rw [this]
        _ = S.z := by group
    have hK4 : InK4 (S.frame.ρ ⟨b, hbN b hb⟩) := by
      refine InK4_of_comm _ (S.rho_four_of_conj_z _ hbz) fun x hx => ?_
      obtain ⟨v, rfl⟩ := S.frame.ψ.surjective x
      have hv3 : (v : G) ∈ S.V3 := S.mem_pre.2 ⟨v.2, by simpa using mem_W3.2 hx⟩
      rw [← S.psi_conj ⟨b, hbN b hb⟩ v, ← map_inv, ← map_mul]
      have hc : b * v * b⁻¹ * (v : G)⁻¹ ∈ S.V1 := by
        have := hF.commutator_conjClosure_le v (le_conjClosure _ _ hv3) b (hUQ (hV3U hb))
        have e : b * v * b⁻¹ * (v : G)⁻¹ = (v * b * (v : G)⁻¹ * b⁻¹)⁻¹ := by group
        rw [e]
        exact S.V1.inv_mem this
      rcases S.mem_V1.1 hc with h | h
      · left
        have : (⟨b * v * b⁻¹, (Subgroup.mem_normalizer_iff.mp (hbN b hb) v).mp v.2⟩ * v⁻¹ :
            ↥V) = 1 := Subtype.ext (by simpa using h)
        rw [this, map_one]
      · right
        have : (⟨b * v * b⁻¹, (Subgroup.mem_normalizer_iff.mp (hbN b hb) v).mp v.2⟩ * v⁻¹ :
            ↥V) = ⟨S.z, S.z_mem_V⟩ := Subtype.ext (by simpa using h)
        rw [this, S.psi_z]
    refine K4_fix_W2 _ hK4 fun x hx => ?_
    obtain ⟨v, rfl⟩ := S.frame.ψ.surjective x
    have hv2 : (v : G) ∈ S.V2 := S.mem_pre.2 ⟨v.2, by simpa using mem_W2.2 hx⟩
    have hcomm : b * v = v * b := by
      have := hVg.1.is_comm.comm ⟨b, conjSub_mono _ S.V3_le_V hb⟩ ⟨v, hV2 hv2⟩
      exact congrArg Subtype.val this
    exact (S.conj_eq_iff ⟨b, hbN b hb⟩ v).1 (by rw [hcomm]; group)
  have hcommV2 : ∀ v ∈ V, ∀ b ∈ conjSub g⁻¹ S.V3, v * b * v⁻¹ * b⁻¹ ∈ S.V2 := by
    intro v hv b hb
    have hbv : b * v * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hbN b hb) v).mp hv
    have hmem : b * v * b⁻¹ * v⁻¹ ∈ S.V2 := by
      refine S.mem_pre.2 ⟨V.mul_mem hbv (V.inv_mem hv), ?_⟩
      have h := S.psi_conj ⟨b, hbN b hb⟩ ⟨v, hv⟩
      have e : (⟨b * v * b⁻¹ * v⁻¹, V.mul_mem hbv (V.inv_mem hv)⟩ : ↥V) =
          ⟨b * v * b⁻¹, hbv⟩ * (⟨v, hv⟩ : ↥V)⁻¹ := rfl
      rw [e, map_mul, h, map_inv]
      rcases hbρ b hb with hρ | hρ
      · rw [hρ, map_one, MulAut.one_apply, mul_inv_cancel]
        exact W2.one_mem
      · rw [hρ]
        exact mem_W2.2 (comm_pa_W2 _)
    have e : v * b * v⁻¹ * b⁻¹ = (b * v * b⁻¹ * v⁻¹)⁻¹ := by
      rw [show (b * v * b⁻¹ * v⁻¹)⁻¹ = v * b * v⁻¹ * b⁻¹ by group]
    rw [e]
    exact S.V2.inv_mem hmem
  have hV2g := S.V2_le_conj_V3 h1326 hg hV2
  have hNV3 : V ≤ Subgroup.normalizer (conjSub g⁻¹ S.V3 : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun v hv b hb => ?_
    have e : v * b * v⁻¹ = (v * b * v⁻¹ * b⁻¹) * b := by group
    rw [e]
    exact (conjSub g⁻¹ S.V3).mul_mem (hV2g (hcommV2 v hv b hb)) hb
  refine hNV3.trans ?_
  rw [conjSub_normalizer, conjSub_normalizer]
  exact conjSub_mono _ (h1323 G T L V S)

theorem V2_le_of_mem {X : Subgroup G} (hz : S.z ∈ X) {y : G} (hyV : y ∈ V) (hyX : y ∈ X)
    (hyW : InW2 (S.frame.ψ ⟨y, hyV⟩)) (hy1 : S.frame.ψ ⟨y, hyV⟩ ≠ 1)
    (hyz : S.frame.ψ ⟨y, hyV⟩ ≠ W4) : S.V2 ≤ X := by
  intro x hx
  obtain ⟨hxV, hxW⟩ := S.mem_pre.1 hx
  have hgen := W2_gen _ hyW hy1 hyz _ (mem_W2.1 hxW)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hgen
  rcases hgen with h | h | h | h
  · have : (⟨x, hxV⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [h, map_one])
    rw [show x = 1 from congrArg Subtype.val this]
    exact X.one_mem
  · have : (⟨x, hxV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := S.frame.ψ.injective (by rw [h, S.psi_z])
    rw [show x = S.z from congrArg Subtype.val this]
    exact hz
  · have : (⟨x, hxV⟩ : ↥V) = ⟨y, hyV⟩ := S.frame.ψ.injective h
    rw [show x = y from congrArg Subtype.val this]
    exact hyX
  · have : (⟨x, hxV⟩ : ↥V) = ⟨y, hyV⟩ * ⟨S.z, S.z_mem_V⟩ :=
      S.frame.ψ.injective (by rw [h, map_mul, S.psi_z])
    rw [show x = y * S.z from congrArg Subtype.val this]
    exact X.mul_mem hyX hz

theorem exists_L1_c3p_pow (k : ℕ) : ∃ l : ↥(Subgroup.normalizer (V : Set G)),
    (l : G) ∈ S.L1 ∧ S.frame.ρ l = c3p ^ k := by
  obtain ⟨l, hl, hρ⟩ := S.exists_L1_c3p
  exact ⟨l ^ k, by simpa using S.L1.pow_mem hl k, by rw [map_pow, hρ]⟩

theorem conjSub_le_normalizer_of_V2 (h1323 : Input1323Two) (h1326 : Input1326Two)
    (h1336 : Input1336) {g : G} (hg : g ∈ S.G1) (hV2 : S.V2 ≤ conjSub g⁻¹ V) :
    conjSub g⁻¹ V ≤ Subgroup.normalizer (V : Set G) := by
  have hz : g * S.z * g⁻¹ = S.z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc g * S.z * g⁻¹ = S.z * g * g⁻¹ := by rw [this]
      _ = S.z := by group
  obtain ⟨v, hvW, hv1, hvz⟩ : ∃ v : W5, InW2 v ∧ v ≠ 1 ∧ v ≠ W4 :=
    ⟨Multiplicative.ofAdd (e2 0 1), by decide +kernel, by decide +kernel, by decide +kernel⟩
  set v' : G := (S.frame.ψ.symm v : G) with hv'
  have hv'V : v' ∈ V := (S.frame.ψ.symm v).2
  have hψv' : S.frame.ψ ⟨v', hv'V⟩ = v := by
    have : (⟨v', hv'V⟩ : ↥V) = S.frame.ψ.symm v := Subtype.ext rfl
    rw [this, MulEquiv.apply_symm_apply]
  have hv'2 : v' ∈ S.V2 := S.mem_pre.2 ⟨hv'V, by rw [hψv']; exact mem_W2.2 hvW⟩
  have hyV : g * v' * g⁻¹ ∈ V := by
    have := hV2 hv'2
    rwa [mem_conjSub, inv_inv] at this
  have hy3 : g * v' * g⁻¹ ∈ S.V3 := S.conj_mem_V3_of_V2 h1326 hg hv'2 hyV
  set y := S.frame.ψ ⟨g * v' * g⁻¹, hyV⟩ with hy
  have hy1 : y ≠ 1 := by
    intro h
    apply hv1
    have : (⟨g * v' * g⁻¹, hyV⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [← hy, h, map_one])
    have e := congrArg Subtype.val this
    have : v' = 1 := by
      have e2 : v' = g⁻¹ * (g * v' * g⁻¹) * g := by group
      rw [e2, show g * v' * g⁻¹ = 1 from e]; group
    rw [← hψv']
    have : (⟨v', hv'V⟩ : ↥V) = 1 := Subtype.ext this
    rw [this, map_one]
  have hyz : y ≠ W4 := by
    intro h
    apply hvz
    have : (⟨g * v' * g⁻¹, hyV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ :=
      S.frame.ψ.injective (by rw [← hy, h, S.psi_z])
    have e := congrArg Subtype.val this
    have hgz' : g⁻¹ * S.z * g = S.z := by
      calc g⁻¹ * S.z * g = g⁻¹ * (g * S.z * g⁻¹) * g := by rw [hz]
        _ = S.z := by group
    have : v' = S.z := by
      have e2 : v' = g⁻¹ * (g * v' * g⁻¹) * g := by group
      rw [e2, show g * v' * g⁻¹ = S.z from e, hgz']
    rw [← hψv']
    have : (⟨v', hv'V⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := Subtype.ext this
    rw [this, S.psi_z]
  have hyW3 : c4 y = 1 := by
    obtain ⟨_, h⟩ := S.mem_pre.1 hy3
    exact mem_W3.1 h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, InW2 (pact (c3p ^ k) y) := by
    rcases exists_c3p_pow_W2 y hyW3 hy1 hyz with h | h | h
    · exact ⟨0, by rw [pow_zero, map_one, MulAut.one_apply]; exact ⟨hyW3, h⟩⟩
    · exact ⟨1, by
        rw [pow_one]
        exact ⟨pact_mem_W3 _ _ c3p_four hyW3, h⟩⟩
    · exact ⟨2, by
        rw [pow_two]
        exact ⟨pact_mem_W3 _ _ (by decide) hyW3, h⟩⟩
  obtain ⟨l, hlL1, hlρ⟩ := S.exists_L1_c3p_pow k
  have hlz : (l : G) * S.z * (l : G)⁻¹ = S.z := S.conj_z_of_normalizes (S.L1_le_NV1 hlL1)
  set h := g⁻¹ * (l : G)⁻¹ with hh
  have hhG1 : h ∈ S.G1 := S.G1.mul_mem (S.G1.inv_mem hg)
    (S.G1.inv_mem (S.G1_eq_normalizer ▸ S.L1_le_NV1 hlL1))
  have hlyV : (l : G) * (g * v' * g⁻¹) * (l : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp l.2 _).mp hyV
  have hψly : S.frame.ψ ⟨(l : G) * (g * v' * g⁻¹) * (l : G)⁻¹, hlyV⟩ = pact (c3p ^ k) y := by
    rw [S.psi_conj l ⟨g * v' * g⁻¹, hyV⟩, hlρ]
  have hV2h : S.V2 ≤ conjSub h⁻¹ V := by
    have hV2sub : S.V2 ≤ conjSub ((l : G) * g) S.V2 := by
      refine S.V2_le_of_mem (y := (l : G) * (g * v' * g⁻¹) * (l : G)⁻¹) ?_ hlyV ?_
        (by rw [hψly]; exact hk) ?_ ?_
      · rw [mem_conjSub]
        have hgz' : g⁻¹ * S.z * g = S.z := by
          calc g⁻¹ * S.z * g = g⁻¹ * (g * S.z * g⁻¹) * g := by rw [hz]
            _ = S.z := by group
        have : ((l : G) * g)⁻¹ * S.z * ((l : G) * g) = g⁻¹ * ((l : G)⁻¹ * S.z * l) * g := by
          group
        rw [this]
        have hlz' : (l : G)⁻¹ * S.z * l = S.z := by
          calc (l : G)⁻¹ * S.z * l = (l : G)⁻¹ * ((l : G) * S.z * (l : G)⁻¹) * l := by rw [hlz]
            _ = S.z := by group
        rw [hlz', hgz']
        exact S.V1_le_V2 (S.mem_V1.2 (Or.inr rfl))
      · rw [mem_conjSub]
        have : ((l : G) * g)⁻¹ * ((l : G) * (g * v' * g⁻¹) * (l : G)⁻¹) * ((l : G) * g) = v' := by
          group
        rw [this]
        exact hv'2
      · rw [hψly]
        intro h1
        apply hy1
        have := congrArg (pact (c3p ^ k)⁻¹) h1
        rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply,
          map_one] at this
      · rw [hψly]
        intro h1
        apply hyz
        have := congrArg (pact (c3p ^ k)⁻¹) h1
        rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply,
          pact_W4 (by rw [Equiv.Perm.inv_eq_iff_eq, c3p_pow_fix4])] at this
    intro x hx
    have hx' := hV2sub hx
    rw [mem_conjSub] at hx'
    rw [hh, mem_conjSub, inv_inv]
    have hmem : g⁻¹ * (l : G)⁻¹ * x * ((g⁻¹ * (l : G)⁻¹))⁻¹ ∈ S.V2 := by
      have : g⁻¹ * (l : G)⁻¹ * x * ((g⁻¹ * (l : G)⁻¹))⁻¹ =
          ((l : G) * g)⁻¹ * x * ((l : G) * g) := by group
      rw [this]
      exact hx'
    exact S.pre_le_V W2 hmem
  have key := S.le_normalizer_conj_of_V2 h1323 h1326 h1336 hhG1 hV2h
  intro b hb
  rw [mem_conjSub, inv_inv] at hb
  have hv : (l : G) * (g * b * g⁻¹) * (l : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp l.2 _).mp hb
  have := key hv
  rw [show h⁻¹ = ((h⁻¹)⁻¹)⁻¹ by rw [inv_inv], mem_normalizer_conjSub_iff] at this
  have e : h⁻¹⁻¹ * ((l : G) * (g * b * g⁻¹) * (l : G)⁻¹) * h⁻¹⁻¹⁻¹ = b := by
    rw [hh]; group
  rwa [e] at this


theorem relIndex_V3 : S.V3.relIndex V = 2 := by
  have h := Subgroup.relIndex_mul_index (H := S.V3) (K := V) S.V3_le_V
  have h2 := Subgroup.card_mul_index S.V3
  have h3 := Subgroup.card_mul_index V
  have hV := S.card_V
  have hV3 := S.card_V3
  rw [Subgroup.relIndex] at h ⊢
  have hcard := Subgroup.card_mul_index (S.V3.subgroupOf V)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.V3_le_V).toEquiv, hV3, hV] at hcard
  omega

theorem mul_inv_mem_V3 {x y : G} (hx : x ∈ V) (hy : y ∈ V) (hx3 : x ∉ S.V3) (hy3 : y ∉ S.V3) :
    x * y⁻¹ ∈ S.V3 := by
  have hc : ∀ {u : G} (hu : u ∈ V), u ∉ S.V3 → c4 (S.frame.ψ ⟨u, hu⟩) ≠ 1 := by
    intro u hu h3 h
    exact h3 (S.mem_pre.2 ⟨hu, mem_W3.2 h⟩)
  have h1 := hc hx hx3
  have h2 := hc hy hy3
  have key : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a * b⁻¹ = 1 := by decide
  refine S.mem_pre.2 ⟨V.mul_mem hx (V.inv_mem hy), mem_W3.2 ?_⟩
  have e : (⟨x * y⁻¹, V.mul_mem hx (V.inv_mem hy)⟩ : ↥V) = ⟨x, hx⟩ * (⟨y, hy⟩ : ↥V)⁻¹ := rfl
  rw [e, map_mul, map_inv, map_mul, map_inv]
  exact key _ _ h1 h2

theorem isPGroup_sup_of_lt (h1323 : Input1323Two) (h1326 : Input1326Two) (h1336 : Input1336)
    {H : Subgroup G} (hH : H ∈ S.Hz) {g : G} (hg : g ∈ H) (hlt : S.V1 < V ⊓ conjSub g⁻¹ V) :
    IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := S.hypF91 h1323 hH
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hVg2 : IsPGroup 2 (conjSub g⁻¹ V) := F7.isPGroup_conjSub S.isPGroup_V
  have hQV : IsPGroup 2 ↥(pCoreOf 2 H ⊔ V) :=
    IsPGroup.to_sup_of_normal_left' hQ2 S.isPGroup_V (hF.V_le_H.trans hQn)
  by_cases hVQ : V ≤ pCoreOf 2 H
  ·
    have hVgQ : conjSub g⁻¹ V ≤ pCoreOf 2 H := by
      have := conjSub_mono g⁻¹ hVQ
      rwa [F7.conjSub_eq_of_mem_normalizer (hQn (H.inv_mem hg))] at this
    exact hQ2.to_le (sup_le hVQ hVgQ)
  by_cases hVgQV : conjSub g⁻¹ V ≤ pCoreOf 2 H ⊔ V
  · exact hQV.to_le (sup_le le_sup_right hVgQV)
  obtain ⟨hV3eq, -⟩ := hF.F95_1 S.relIndex_V3 hVQ
  have hint : V ⊓ conjSub g⁻¹ V ≤ S.V3 := by
    intro x hx
    rw [hV3eq]
    refine ⟨hx.1, ?_⟩
    by_contra hxQ
    apply hVgQV
    have hV3Q : S.V3 ≤ pCoreOf 2 H := by
      rw [hV3eq]; exact inf_le_right
    have hV3gQ : conjSub g⁻¹ S.V3 ≤ pCoreOf 2 H := by
      have := conjSub_mono g⁻¹ hV3Q
      rwa [F7.conjSub_eq_of_mem_normalizer (hQn (H.inv_mem hg))] at this
    intro y hy
    by_cases hyQ : y ∈ pCoreOf 2 H
    · exact le_sup_left (a := pCoreOf 2 H) hyQ
    ·
      have hyx : y * x⁻¹ ∈ conjSub g⁻¹ V :=
        (conjSub g⁻¹ V).mul_mem hy ((conjSub g⁻¹ V).inv_mem hx.2)
      have hyxQ : y * x⁻¹ ∈ conjSub g⁻¹ S.V3 := by
        have hxV3 : x ∉ conjSub g⁻¹ S.V3 := fun h => hxQ (hV3gQ h)
        have hyV3 : y ∉ conjSub g⁻¹ S.V3 := fun h => hyQ (hV3gQ h)
        rw [mem_conjSub, inv_inv] at hxV3 hyV3 ⊢
        have hx' : g * x * g⁻¹ ∈ V := by
          have : x ∈ conjSub g⁻¹ V := hx.2
          rwa [mem_conjSub, inv_inv] at this
        have hy' : g * y * g⁻¹ ∈ V := by rwa [mem_conjSub, inv_inv] at hy
        have := S.mul_inv_mem_V3 hy' hx' hyV3 hxV3
        have e : g * (y * x⁻¹) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
        rw [e]
        exact this
      have : y = (y * x⁻¹) * x := by group
      rw [this]
      exact Subgroup.mul_mem_sup (hV3gQ hyxQ) hx.1
  obtain ⟨w, hwI, hwV1⟩ := IsConcreteLE.exists_of_lt hlt
  have hwV : w ∈ V := hwI.1
  have hw3 : w ∈ S.V3 := hint hwI
  have hw1 : S.frame.ψ ⟨w, hwV⟩ ≠ 1 := by
    intro h1
    apply hwV1
    have : (⟨w, hwV⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [h1, map_one])
    rw [S.mem_V1]
    exact Or.inl (congrArg Subtype.val this)
  have hwz : S.frame.ψ ⟨w, hwV⟩ ≠ W4 := by
    intro h1
    apply hwV1
    have : (⟨w, hwV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := S.frame.ψ.injective (by rw [h1, S.psi_z])
    rw [S.mem_V1]
    exact Or.inr (congrArg Subtype.val this)
  have hwW3 : c4 (S.frame.ψ ⟨w, hwV⟩) = 1 := by
    obtain ⟨_, h⟩ := S.mem_pre.1 hw3
    exact mem_W3.1 h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, InW2 (pact (c3p ^ k) (S.frame.ψ ⟨w, hwV⟩)) := by
    rcases exists_c3p_pow_W2 _ hwW3 hw1 hwz with h | h | h
    · exact ⟨0, by rw [pow_zero, map_one, MulAut.one_apply]; exact ⟨hwW3, h⟩⟩
    · exact ⟨1, by rw [pow_one]; exact ⟨pact_mem_W3 _ _ c3p_four hwW3, h⟩⟩
    · exact ⟨2, by rw [pow_two]; exact ⟨pact_mem_W3 _ _ (by decide) hwW3, h⟩⟩
  obtain ⟨l, hlL1, hlρ⟩ := S.exists_L1_c3p_pow k
  have hlz : (l : G) * S.z * (l : G)⁻¹ = S.z := S.conj_z_of_normalizes (S.L1_le_NV1 hlL1)
  have hlH : (l : G) ∈ H := le_sup_left.trans hH.1.1 hlL1
  have hlwV : (l : G) * w * (l : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp l.2 w).mp hwV
  have hψlw : S.frame.ψ ⟨(l : G) * w * (l : G)⁻¹, hlwV⟩ = pact (c3p ^ k) (S.frame.ψ ⟨w, hwV⟩) := by
    rw [S.psi_conj l ⟨w, hwV⟩, hlρ]
  have hV2 : S.V2 ≤ conjSub (g * (l : G)⁻¹)⁻¹ V := by
    refine S.V2_le_of_mem ?_ hlwV ?_ (by rw [hψlw]; exact hk) ?_ ?_
    · rw [mem_conjSub, inv_inv]
      have hzI : S.z ∈ conjSub g⁻¹ V := (hlt.le (S.mem_V1.2 (Or.inr rfl))).2
      rw [mem_conjSub, inv_inv] at hzI
      have : g * (l : G)⁻¹ * S.z * (g * (l : G)⁻¹)⁻¹ = g * ((l : G)⁻¹ * S.z * l) * g⁻¹ := by
        group
      rw [this]
      have hlz' : (l : G)⁻¹ * S.z * l = S.z := by
        calc (l : G)⁻¹ * S.z * l = (l : G)⁻¹ * ((l : G) * S.z * (l : G)⁻¹) * l := by rw [hlz]
          _ = S.z := by group
      rw [hlz']
      exact hzI
    · rw [mem_conjSub, inv_inv]
      have hwg : w ∈ conjSub g⁻¹ V := hwI.2
      rw [mem_conjSub, inv_inv] at hwg
      have : g * (l : G)⁻¹ * ((l : G) * w * (l : G)⁻¹) * (g * (l : G)⁻¹)⁻¹ = g * w * g⁻¹ := by
        group
      rw [this]
      exact hwg
    · rw [hψlw]
      intro h1
      apply hw1
      have := congrArg (pact (c3p ^ k)⁻¹) h1
      rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply,
        map_one] at this
    · rw [hψlw]
      intro h1
      apply hwz
      have := congrArg (pact (c3p ^ k)⁻¹) h1
      rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply,
        pact_W4 (by rw [Equiv.Perm.inv_eq_iff_eq, c3p_pow_fix4])] at this
  have hg' : g * (l : G)⁻¹ ∈ S.G1 := hH.2.1 (H.mul_mem hg (H.inv_mem hlH))
  have hN := S.conjSub_le_normalizer_of_V2 h1323 h1326 h1336 hg' hV2
  have hP : IsPGroup 2 ↥(V ⊔ conjSub (g * (l : G)⁻¹)⁻¹ V) :=
    IsPGroup.to_sup_of_normal_left' S.isPGroup_V (F7.isPGroup_conjSub S.isPGroup_V) hN
  have e : conjSub (l : G)⁻¹ (V ⊔ conjSub (g * (l : G)⁻¹)⁻¹ V) = V ⊔ conjSub g⁻¹ V := by
    rw [conjSub_sup, F7.conjSub_eq_of_mem_normalizer (Subgroup.inv_mem _ l.2), ← conjSub_mul]
    congr 2
    group
  rw [← e]
  exact F7.isPGroup_conjSub hP

theorem hyp_F956 (h1323 : Input1323Two) (H : Subgroup G) :
    ⁅V, H ⊓ Subgroup.centralizer (S.V3 : Set G)⁆ ≤ S.V1 := by
  have : ⁅V, H ⊓ Subgroup.centralizer (S.V3 : Set G)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    exact S.mem_centralizer_V_of_V3
      (h1323 G T L V S (Subgroup.centralizer_le_normalizer _ hx.2)) hx.2
  rw [this]
  exact bot_le

end Setting

end CFSG.Quasithin.H13.A5
