module

public import CFSG.Quasithin.Background.HMathieuO2Data
public import CFSG.Quasithin.H13.StatementsL6
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Setting811 (T L V M : Subgroup G) : Prop where
  sylow : IsSylowTwoOf T ⊤
  elem : IsElemAbelian 2 V
  V_le_T : V ≤ T
  LT_le_normalizer : L ⊔ T ≤ Subgroup.normalizer (V : Set G)
  normalizer_le : Subgroup.normalizer (V : Set G) ≤ M
  LT_le : L ⊔ T ≤ M
  le_normalizer_L : M ≤ Subgroup.normalizer (L : Set G)
  ti : IsTISetUnder V M
  q_eq : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T)
  normalizer_char_le : ∀ C : Subgroup G, C ≤ T ⊓ Subgroup.centralizer (V : Set G) → C ≠ ⊥ →
    (C.subgroupOf (T ⊓ Subgroup.centralizer (V : Set G))).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ M
  quasisimple : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  charTwo : CharTwo M
  localSQTK : ∀ P : Subgroup G, pCoreOf 2 P ≠ ⊥ → SQTKGroup ↥P
  card : Nat.card V = 2 ^ 10 ∨ Nat.card V = 2 ^ 11

namespace Setting811

variable {T L V M : Subgroup G} (S : Setting811 T L V M)

include S

theorem L_le_normalizer : L ≤ Subgroup.normalizer (V : Set G) :=
  le_sup_left.trans S.LT_le_normalizer

theorem T_le_normalizer : T ≤ Subgroup.normalizer (V : Set G) :=
  le_sup_right.trans S.LT_le_normalizer

theorem L_le_M : L ≤ M := le_sup_left.trans S.LT_le

theorem T_le_M : T ≤ M := le_sup_right.trans S.LT_le

end Setting811

theorem not_isPGroup_two_of_card {X : Type*} [Group X] [Finite X] {N : ℕ}
    (hN : N = 20160 ∨ N = 443520) (hX : Nat.card X = N) : ¬ IsPGroup 2 X := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h.exists_card_eq
  have h3 : 3 ∣ Nat.card X := by rw [hX]; rcases hN with rfl | rfl <;> norm_num
  rw [hk] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at this

section Image

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem autI_inf_centralizer (L : Subgroup G) (x : IntMod V hV) :
    autI hV (L ⊓ Subgroup.centralizer ({x.val} : Set G)) = stabV (autI hV L) x := by
  ext φ
  refine Iff.trans ?_ mem_stabV.symm
  constructor
  · intro h
    obtain ⟨g, ⟨hgL, hgx⟩, rfl⟩ := (mem_autI hV).1 h
    refine ⟨(mem_autI hV).2 ⟨g, hgL, rfl⟩, IntMod.val_injective ?_⟩
    rw [convI_apply_val]
    have := Subgroup.mem_centralizer_iff.1 hgx x.val rfl
    rw [← this, mul_inv_cancel_right]
  · rintro ⟨h, hφx⟩
    obtain ⟨g, hgL, rfl⟩ := (mem_autI hV).1 h
    refine (mem_autI hV).2 ⟨g, ⟨hgL, ?_⟩, rfl⟩
    show (g : G) ∈ Subgroup.centralizer ({x.val} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    have h1 := congrArg IntMod.val hφx
    rw [convI_apply_val] at h1
    calc x.val * (g : G) = (g * x.val * (g : G)⁻¹) * g := by rw [h1]
      _ = g * x.val := by group

theorem autI_perfectCore {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    autI hV (perfectCore K) = perfectCore (autI hV K) := by
  have := finite_mulAut (IntMod V hV)
  rw [autI, autI, perfectCore_map_subgroupOf hK]

end Image

namespace Setting811

variable {T L V M : Subgroup G} (S : Setting811 T L V M)

abbrev cH (x : IntMod V S.elem) : Subgroup G := Subgroup.centralizer ({x.val} : Set G)

abbrev cLH (x : IntMod V S.elem) : Subgroup G := perfectCore (L ⊓ S.cH x)

noncomputable abbrev cY (x : IntMod V S.elem) : Subgroup (MulAut (IntMod V S.elem)) :=
  perfectCore (stabV (autI S.elem L) x)

theorem LH_le (x : IntMod V S.elem) : S.cLH x ≤ L ⊓ S.cH x := perfectCore_le _

theorem LH_le_normalizer (x : IntMod V S.elem) :
    S.cLH x ≤ Subgroup.normalizer (V : Set G) :=
  (S.LH_le x).trans (inf_le_left.trans S.L_le_normalizer)

theorem autI_LH (x : IntMod V S.elem) : autI S.elem (S.cLH x) = S.cY x := by
  rw [autI_perfectCore S.elem (inf_le_left.trans S.L_le_normalizer),
    autI_inf_centralizer S.elem L]

theorem Y_le (x : IntMod V S.elem) : S.cY x ≤ autI S.elem L :=
  (perfectCore_le _).trans inf_le_left

theorem MH_le_normalizer_LH (x : IntMod V S.elem) :
    S.cH x ⊓ M ≤ Subgroup.normalizer (S.cLH x : Set G) := by
  refine le_trans ?_ (normalizer_le_normalizer_perfectCore _)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hgL := Subgroup.mem_normalizer_iff.1 (S.le_normalizer_L hg.2) y
  have hgH := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hg.1) y
  exact ⟨fun hy => ⟨hgL.1 hy.1, hgH.1 hy.2⟩, fun hy => ⟨hgL.2 hy.1, hgH.2 hy.2⟩⟩

theorem LH_le_MH (x : IntMod V S.elem) : S.cLH x ≤ S.cH x ⊓ M :=
  fun _ hl => ⟨((S.LH_le x) hl).2, S.L_le_M ((S.LH_le x) hl).1⟩

end Setting811

omit [Finite G] in
theorem mem_pCoreOf_iff' {X : Subgroup G} (y : ↥X) :
    (y : G) ∈ pCoreOf 2 X ↔ y ∈ CFSG.pCore 2 ↥X := CFSG.mem_openPCoreOf_iff y

theorem eq_one_of_isPGroup_of_perfect {X : Type*} [Group X] [Finite X]
    (hp : IsPGroup 2 X) (hc : commutator X = ⊤) (g : X) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent X := hp.isNilpotent
  obtain ⟨n, hn⟩ := (Group.isSolvable_def X).1 inferInstance
  have htop : ∀ k, derivedSeries X k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih]; exact hc
  rw [htop n] at hn
  have := Subgroup.mem_top g
  rw [hn, Subgroup.mem_bot] at this
  exact this

omit [Finite G] in
theorem commutator_coe_eq_top_of_perfect {H : Subgroup G} (hH : ⁅H, H⁆ = H) :
    commutator ↥H = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    hH]

theorem commutator_quotient_eq_top {X : Type*} [Group X] (hX : commutator X = ⊤)
    (N : Subgroup X) [N.Normal] : commutator (X ⧸ N) = ⊤ := by
  have h := congrArg (Subgroup.map (QuotientGroup.mk' N)) hX
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective N)] at h
  rw [commutator_def]
  exact h

theorem center_eq_bot_of_card {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] {N : ℕ}
    (hN : N = 20160 ∨ N = 443520) (hX : Nat.card X = N) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
    let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hcomm }
    have hp := IsSimpleGroup.prime_card (α := X)
    rw [hX] at hp
    rcases hN with rfl | rfl <;> norm_num at hp

namespace Setting811

variable {T L V M : Subgroup G} (S : Setting811 T L V M) {N : ℕ}
  {x : IntMod V S.elem}

theorem pCoreOf_LH_le (hN : N = 20160 ∨ N = 443520) (hx : O2Data (autI S.elem L) x N) :
    pCoreOf 2 (S.cLH x) ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup ↥(S.cY x) := hx.1
  set P := pCoreOf 2 (S.cLH x)
  have hPL : P ≤ S.cLH x := pCoreOf_le 2 _
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPL.trans (S.LH_le_normalizer x)
  have hle : autI S.elem P ≤ S.cY x := (autI_mono S.elem hPL).trans (S.autI_LH x).le
  have hp : IsPGroup 2 ↥(autI S.elem P) :=
    ((pCoreOf_isPGroup 2 (S.cLH x)).comap_subtype).map _
  have hnorm : ((autI S.elem P).subgroupOf (S.cY x)).Normal := by
    refine ⟨fun φ hφ y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hφ ⊢
    have hy : (y : MulAut (IntMod V S.elem)) ∈ autI S.elem (S.cLH x) := by
      rw [S.autI_LH x]; exact y.2
    obtain ⟨l, hl, hly⟩ := (mem_autI S.elem).1 hy
    obtain ⟨q, hq, hqφ⟩ := (mem_autI S.elem).1 hφ
    have hlq : (l : G) * q * (l : G)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (S.cLH x) hl) q).1 hq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hly, ← hqφ, ← map_mul, ← map_inv, ← map_mul]
    exact (mem_autI S.elem).2 ⟨l * q * l⁻¹, by simpa using hlq, rfl⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((autI S.elem P).subgroupOf (S.cY x)) with
    h | h
  · have hbot : autI S.elem P = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at h
      exact eq_bot_iff.2 fun φ hφ => (Subgroup.disjoint_def.1 h) hφ (hle hφ)
    exact (autI_eq_bot_iff S.elem hPN).1 hbot
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at h
    exact not_isPGroup_two_of_card hN hx.2.1 (hp.to_le h)

theorem commutator_V_LH (hx : O2Data (autI S.elem L) x N) : ⁅V, S.cLH x⁆ = V := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro v hv l hl
    have hl' := Subgroup.mem_normalizer_iff.1 (S.LH_le_normalizer x hl) v⁻¹
    have : l * v⁻¹ * l⁻¹ ∈ V := hl'.1 (V.inv_mem hv)
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc l]
    exact V.mul_mem hv this
  · intro v hv
    have key : ∀ w ∈ Mathieu.commV (S.cY x), (IntMod.val w) ∈ ⁅V, S.cLH x⁆ := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem w hw =>
        obtain ⟨y, hy, u, rfl⟩ := hw
        rw [← S.autI_LH x] at hy
        obtain ⟨g, hg, rfl⟩ := (mem_autI S.elem).1 hy
        rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hg u.val_mem
      | one => exact Subgroup.one_mem _
      | mul a b _ _ ha hb =>
        rw [IntMod.val_mul]
        exact Subgroup.mul_mem _ ha hb
      | inv a _ ha =>
        rw [IntMod.val_inv]
        exact Subgroup.inv_mem _ ha
    have htop : Mathieu.commV (S.cY x) = ⊤ := hx.2.2.1
    exact key (IntMod.mk S.elem ⟨v, hv⟩) (by rw [htop]; exact Subgroup.mem_top _)

theorem V_le_MH : V ≤ S.cH x ⊓ M := by
  intro v hv
  refine ⟨Subgroup.mem_centralizer_iff.2 ?_, S.T_le_M (S.V_le_T hv)⟩
  rintro _ rfl
  exact IntMod.val_comm x (IntMod.mk S.elem ⟨v, hv⟩)

theorem V_le_LH (hx : O2Data (autI S.elem L) x N) : V ≤ S.cLH x := by
  refine (S.commutator_V_LH hx).ge.trans ?_
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have hvN := S.MH_le_normalizer_LH x (S.V_le_MH hv)
  have : v * l * v⁻¹ ∈ S.cLH x := (Subgroup.mem_normalizer_iff.1 hvN l).1 hl
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ hl)

theorem mem_centralizer_of_comm (hx : O2Data (autI S.elem L) x N) {c : G}
    (hcN : c ∈ Subgroup.normalizer (V : Set G))
    (hc : ∀ l ∈ S.cLH x, l * c * l⁻¹ * c⁻¹ ∈ Subgroup.centralizer (V : Set G)) :
    c ∈ Subgroup.centralizer (V : Set G) := by
  have hmem : convI S.elem ⟨c, hcN⟩ ∈ Subgroup.centralizer (S.cY x : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← S.autI_LH x] at hy
    obtain ⟨g, hg, rfl⟩ := (mem_autI S.elem).1 hy
    have h1 := (convI_eq_one_iff S.elem (g * ⟨c, hcN⟩ * g⁻¹ * (⟨c, hcN⟩)⁻¹)).2 (hc g hg)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    rw [← mul_inv_eq_one, ← mul_inv_eq_one]
    calc convI S.elem g * convI S.elem ⟨c, hcN⟩ *
          (convI S.elem ⟨c, hcN⟩ * convI S.elem g)⁻¹ * 1 =
        convI S.elem g * convI S.elem ⟨c, hcN⟩ * (convI S.elem g)⁻¹ *
          (convI S.elem ⟨c, hcN⟩)⁻¹ := by group
      _ = 1 := h1
  rw [hx.2.2.2, Subgroup.mem_bot, convI_eq_one_iff] at hmem
  exact hmem

theorem autI_L_not_isPGroup (hN : N = 20160 ∨ N = 443520) (hx : O2Data (autI S.elem L) x N) :
    ¬ IsPGroup 2 ↥(autI S.elem L) := fun h =>
  not_isPGroup_two_of_card hN hx.2.1 (h.to_le (S.Y_le x))

theorem commutator_mem_pCoreOf (hN : N = 20160 ∨ N = 443520) (hx : O2Data (autI S.elem L) x N)
    {k l : G} (hk : k ∈ L ⊓ Subgroup.centralizer (V : Set G)) (hl : l ∈ L) :
    ⁅k, l⁆ ∈ pCoreOf 2 L := by
  have : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let Nn : Subgroup ↥L := (L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L
  have hNn : Nn.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 a.2) (L.inv_mem g.2), Subgroup.mem_centralizer_iff.2 ?_⟩
    intro v hv
    have hgN := S.L_le_normalizer g.2
    have hv' : (g : G)⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff''.1 hgN v).1 hv
      exact this
    have hcomm := Subgroup.mem_centralizer_iff.1 ha.2 _ hv'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc v * (g * a * (g : G)⁻¹) = g * ((g : G)⁻¹ * v * g * a) * (g : G)⁻¹ := by group
      _ = g * (a * ((g : G)⁻¹ * v * g)) * (g : G)⁻¹ := by rw [← hcomm]
      _ = g * a * (g : G)⁻¹ * v := by group
  have hmap : (Nn.map π).Normal := hNn.map π hπ
  rcases CFSG.LocalCores.quasisimple_normal_subgroups S.quasisimple hmap with h | h
  · exfalso
    apply S.autI_L_not_isPGroup hN hx
    intro φ
    obtain ⟨g, hgL, hgφ⟩ := (mem_autI S.elem).1 φ.2
    obtain ⟨n, hn, hnπ⟩ : ∃ n ∈ Nn, π n = π ⟨g, hgL⟩ := by
      have : π ⟨g, hgL⟩ ∈ Nn.map π := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, e⟩ := this
      exact ⟨n, hn, e⟩
    have ho : (n⁻¹ * ⟨g, hgL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := QuotientGroup.eq.1 hnπ
    obtain ⟨k₂, hk₂⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, ho⟩
    refine ⟨k₂, Subtype.ext ?_⟩
    have hk2' : ((n⁻¹ * ⟨g, hgL⟩ : ↥L) : G) ^ 2 ^ k₂ = 1 := by
      have := congrArg (fun z : CFSG.pCore 2 ↥L => ((z : ↥L) : G)) hk₂
      simpa using this
    have hnC : (n : G) ∈ Subgroup.centralizer (V : Set G) := (Subgroup.mem_subgroupOf.1 hn).2
    have hnN : (n : G) ∈ Subgroup.normalizer (V : Set G) := S.L_le_normalizer n.2
    have hoN : ((n⁻¹ * ⟨g, hgL⟩ : ↥L) : G) ∈ Subgroup.normalizer (V : Set G) :=
      S.L_le_normalizer (n⁻¹ * ⟨g, hgL⟩ : ↥L).2
    have hconv : convI S.elem g = convI S.elem ⟨_, hoN⟩ := by
      have e : (g : Subgroup.normalizer (V : Set G)) = ⟨n, hnN⟩ * ⟨_, hoN⟩ := by
        apply Subtype.ext
        simp
      calc convI S.elem g = convI S.elem (⟨n, hnN⟩ * ⟨_, hoN⟩) := congrArg _ e
        _ = convI S.elem ⟨_, hoN⟩ := by
          rw [map_mul, (convI_eq_one_iff S.elem _).2 hnC, one_mul]
    have h1 : (⟨_, hoN⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ k₂ = 1 := Subtype.ext hk2'
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hgφ, hconv, ← map_pow, h1, map_one]
  · have hkL : (⟨k, hk.1⟩ : ↥L) ∈ Nn := Subgroup.mem_subgroupOf.2 hk
    have hc : π ⟨k, hk.1⟩ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := h ⟨_, hkL, rfl⟩
    have h1 : π ⁅(⟨k, hk.1⟩ : ↥L), ⟨l, hl⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 hc _).symm
    have h2 : ⁅(⟨k, hk.1⟩ : ↥L), ⟨l, hl⟩⁆ ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).1 h1
    have := (mem_pCoreOf_iff' _).2 h2
    simpa [commutatorElement_def] using this

end Setting811

end CFSG.Quasithin.H13
