module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QCoord
public import CFSG.Quasithin.Vol2.Ch10SecACoprime

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL diagSL coe_diagSL diagSL_conj
  unipSL_mul_self unipSL_mulVec diagSL_mulVec unipSL_zero)
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_mem_ch6 [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have h1 : g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨y, hy, hyx⟩ := h1
  have : y = x := by simpa [MulAut.conj_apply] using hyx
  rw [← this]
  exact hy

theorem fixed_of_coord_ch6 {L S V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hSL : S ≤ L) (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    {F : Type} [Field F] [CharP F 2] (ψ : ↥(autOn L V) ≃* SL(2, F))
    (Y : ↥V →* Multiplicative (Fin 2 → F)) (hYs : Function.Surjective Y)
    (hYk : ∀ x : ↥V, Y x = 1 ↔ (x : G) ∈ Subgroup.centralizer (L : Set G))
    (hYe : ∀ (x : ↥(autOn L V)) (w : ↥V), Multiplicative.toAdd (Y ((x : MulAut ↥V) w)) =
      (ψ x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (Y w)))
    (hYS : ∀ x : ↥(autOn L V), (x : MulAut ↥V) ∈ autOn S V ↔ ∃ b : F, ψ x = unipSL b)
    {u : G} (hu : u ∈ S) (v : ↥V) (hv : Multiplicative.toAdd (Y v) 1 = 0) :
    u * v * u⁻¹ = v := by
  set a : ↥(autOn L V) := ⟨A4.actionOn V L hLV ⟨u, hSL hu⟩,
    (A4.mem_autOn_iff hLV).mpr ⟨_, rfl⟩⟩ with ha
  have hav : ∀ w : ↥V, (((a : MulAut ↥V) w : ↥V) : G) = u * w * u⁻¹ := fun w => rfl
  have haS : (a : MulAut ↥V) ∈ autOn S V :=
    (A4.mem_autOn_iff (hSL.trans hLV)).mpr ⟨⟨u, hu⟩, rfl⟩
  obtain ⟨b, hb⟩ := (hYS a).mp haS
  have haa : a * a = 1 := ψ.injective (by rw [map_mul, hb, unipSL_mul_self, map_one])
  have haa' : ∀ w : ↥V, (a : MulAut ↥V) ((a : MulAut ↥V) w) = w := fun w => by
    have := congrArg (fun x : ↥(autOn L V) => (x : MulAut ↥V) w) haa
    simpa using this
  have hcV : ∀ x y : ↥V, x * y = y * x := fun x y => Subtype.ext (hVc x x.2 y y.2)
  have hsq : ∀ x : ↥V, x * x = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two]
    exact hV2 x x.2)
  have hinv : ∀ x : ↥V, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_left (hsq x)
  suffices hfix : (a : MulAut ↥V) v = v by
    rw [← hav, hfix]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := ψ.injective (by rw [hb, hb0, unipSL_zero, map_one])
    rw [ha1]
    rfl
  obtain ⟨x, hx⟩ : ∃ x, x = Multiplicative.toAdd (Y v) 0 := ⟨_, rfl⟩
  have hYv : Multiplicative.toAdd (Y v) = ![x, 0] := by
    ext i
    fin_cases i
    · exact hx.symm
    · exact hv
  obtain ⟨w, hw⟩ := hYs (Multiplicative.ofAdd ![0, x / b])
  have hYw₁ : Multiplicative.toAdd (Y ((a : MulAut ↥V) w)) = ![x, x / b] := by
    rw [hYe, hb, coe_unipSL, hw, toAdd_ofAdd, unipSL_mulVec]
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        zero_add]
      field_simp
    · simp
  obtain ⟨c, hc⟩ : ∃ c : ↥V, c = v * ((a : MulAut ↥V) w)⁻¹ * w := ⟨_, rfl⟩
  have hYc : Y c = 1 := by
    apply Multiplicative.toAdd.injective
    rw [hc, Y.map_mul, toAdd_mul, Y.map_mul, toAdd_mul, Y.map_inv, toAdd_inv, hYv, hYw₁, hw,
      toAdd_ofAdd, toAdd_one]
    ext i
    fin_cases i <;> simp
  have hcL := (hYk c).mp hYc
  have hac : (a : MulAut ↥V) c = c := by
    apply Subtype.ext
    rw [hav]
    have hcomm := Subgroup.mem_centralizer_iff.mp hcL u (hSL hu)
    rw [hcomm, mul_inv_cancel_right]
  have hvc : v = c * w⁻¹ * (a : MulAut ↥V) w := by rw [hc]; group
  rw [hvc, map_mul, map_mul, map_inv, hac, haa', hinv ((a : MulAut ↥V) w), hinv w, mul_assoc,
    mul_assoc, hcV ((a : MulAut ↥V) w) w]

theorem le_normalizer_commutator_ch6 [Finite G] {A B X : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_of_conj_mem_ch6
  intro x hx
  have hmapA : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hA hg) a).mp ha
  have hmapB : B.map (MulAut.conj g).toMonoidHom ≤ B := by
    rintro _ ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hB hg) b).mp hb
  have h1 : g * x * g⁻¹ ∈ (⁅A, B⁆).map (MulAut.conj g).toMonoidHom := ⟨x, hx, by simp⟩
  rw [Subgroup.map_commutator] at h1
  exact Subgroup.commutator_mono hmapA hmapB h1

theorem le_normalizer_centralizer_ch6 {H S : Subgroup G}
    (h : H ≤ Subgroup.normalizer (S : Set G)) :
    H ≤ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  intro g hg
  have hS := Subgroup.mem_normalizer_iff.mp (h hg)
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := (hS (g⁻¹ * s * g)).mpr (by simpa [mul_assoc] using hs)
    have e := hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [e]
      _ = g * c * g⁻¹ * s := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have e := hc _ ((hS s).mp hs)
    have e' : g * (s * c) * g⁻¹ = g * (c * s) * g⁻¹ := by
      calc g * (s * c) * g⁻¹ = (g * s * g⁻¹) * (g * c * g⁻¹) := by group
        _ = (g * c * g⁻¹) * (g * s * g⁻¹) := e
        _ = g * (c * s) * g⁻¹ := by group
    simpa using e'

theorem IsNatQuotCh5.exists_fixed_ch6 [Finite G] {T L V : Subgroup G} {n : ℕ}
    (h : IsNatQuotCh5 L V n) (hn : 2 ≤ n) (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hVT : V ≤ T) (hS : IsSylowTwoOf (T ⊓ L) L)
    (hCL : L ⊓ Subgroup.centralizer (V : Set G) ≤ T) :
    ∃ z ∈ V, z ∈ Subgroup.centralizer (T : Set G) ∧ z ∉ Subgroup.centralizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.1
  have hinvV : ∀ a ∈ V, a⁻¹ = a := fun a ha =>
    inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hV2 a ha)
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have h1 := hinvV (a * b) (V.mul_mem ha hb)
    rw [mul_inv_rev, hinvV a ha, hinvV b hb] at h1
    exact h1.symm
  obtain ⟨F, _, _, _, hF, ψ, Y, hYs, hYk, hYe, hYS⟩ := h.exists_sylowCoord hS
  set S := T ⊓ L with hSdef
  have hSL : S ≤ L := inf_le_right
  have hST : S ≤ T := inf_le_left
  have hSV : S ≤ Subgroup.normalizer (V : Set G) := hSL.trans hLV
  let act : ↥L →* ↥(autOn L V) := (A4.actionOn V L hLV).codRestrict (autOn L V)
    (fun l => (A4.mem_autOn_iff hLV).mpr ⟨l, rfl⟩)
  have hact : ∀ (l : ↥L) (w : ↥V), ((((act l : ↥(autOn L V)) : MulAut ↥V) w : ↥V) : G) =
      l * w * (l : G)⁻¹ := fun l w => rfl
  have hsurj : ∀ x : ↥(autOn L V), ∃ l : ↥L, act l = x := fun x => by
    obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLV).mp x.2
    exact ⟨l, Subtype.ext hl⟩
  have hSact : ∀ s (hs : s ∈ S), ∃ b : F, ψ (act ⟨s, hSL hs⟩) = unipSL b := fun s hs =>
    (hYS _).mp ((A4.mem_autOn_iff hSV).mpr ⟨⟨s, hs⟩, rfl⟩)
  have hmemS : ∀ l : ↥L, (∃ b : F, ψ (act l) = unipSL b) → (l : G) ∈ S := by
    intro l hl
    obtain ⟨s, hs⟩ := (A4.mem_autOn_iff hSV).mp ((hYS (act l)).mpr hl)
    have hc : (s : G)⁻¹ * l ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.inv_mem (hSL s.2)) l.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have e : (s : G) * v * (s : G)⁻¹ = l * v * (l : G)⁻¹ :=
        congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hs
      calc v * ((s : G)⁻¹ * l) = (s : G)⁻¹ * ((s : G) * v * (s : G)⁻¹) * l := by group
        _ = (s : G)⁻¹ * (l * v * (l : G)⁻¹) * l := by rw [e]
        _ = (s : G)⁻¹ * l * v := by group
    have hlT : (l : G) ∈ T := by
      have e : (l : G) = s * ((s : G)⁻¹ * l) := by group
      rw [e]
      exact T.mul_mem (hST s.2) (hCL hc)
    exact ⟨hlT, l.2⟩
  have hfix : ∀ s ∈ S, ∀ v : ↥V, Multiplicative.toAdd (Y v) 1 = 0 → s * v * s⁻¹ = v :=
    fun s hs v hv => fixed_of_coord_ch6 hLV hSL hV2 hVc ψ Y hYs hYk hYe hYS hs v hv
  obtain ⟨w₀, hw₀⟩ := hYs (Multiplicative.ofAdd ![1, 0])
  have hw₀S : (w₀ : G) ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have e := hfix s hs w₀ (by rw [hw₀]; simp)
    calc s * (w₀ : G) = s * w₀ * s⁻¹ * s := by group
      _ = w₀ * s := by rw [e]
  obtain ⟨μ, hμ0, hμ1⟩ : ∃ μ : F, μ ≠ 0 ∧ μ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsurjB : Function.Surjective (fun b : Bool => if b then (1 : F) else 0) := by
      intro μ
      by_cases h0 : μ = 0
      · exact ⟨false, by simp [h0]⟩
      · exact ⟨true, by simp [hcon μ h0]⟩
    have : Fintype F := Fintype.ofFinite F
    have h1 := Fintype.card_le_of_surjective _ hsurjB
    rw [Fintype.card_bool, ← Nat.card_eq_fintype_card, hF] at h1
    have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨l, hl⟩ := hsurj (ψ.symm (diagSL hμ0))
  have hψl : ψ (act l) = diagSL hμ0 := by rw [hl, MulEquiv.apply_symm_apply]
  have hlS : (l : G) ∈ Subgroup.normalizer (S : Set G) := by
    apply mem_normalizer_of_conj_mem_ch6
    intro s hs
    obtain ⟨b, hb⟩ := hSact s hs
    have hls : (l : G) * s * (l : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem l.2 (hSL hs)) (L.inv_mem l.2)
    have e : act ⟨(l : G) * s * (l : G)⁻¹, hls⟩ = act l * act ⟨s, hSL hs⟩ * (act l)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    refine hmemS ⟨_, hls⟩ ⟨μ ^ 2 * b, ?_⟩
    rw [e, map_mul, map_mul, map_inv, hψl, hb, diagSL_conj]
  have hlw₀ : (l : G) * w₀ ≠ w₀ * l := by
    intro hc
    have hfx : ((act l : ↥(autOn L V)) : MulAut ↥V) w₀ = w₀ := by
      apply Subtype.ext
      rw [hact, hc, mul_inv_cancel_right]
    have e := hYe (act l) w₀
    rw [hfx, hψl, coe_diagSL, hw₀, toAdd_ofAdd, diagSL_mulVec] at e
    have e0 := congrFun e 0
    simp only [Fin.isValue, Matrix.cons_val_zero, mul_one] at e0
    exact hμ1 e0.symm
  set B := borelL T L with hBdef
  have hBL : B ≤ L := inf_le_left
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := inf_le_right
  have hSB : S ≤ B := le_inf hSL Subgroup.le_normalizer
  have hlB : (l : G) ∈ B := ⟨l.2, hlS⟩
  set Yh := V ⊓ Subgroup.centralizer (S : Set G) with hYhdef
  have hBYh : B ≤ Subgroup.normalizer (Yh : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hLV (hBL hb), le_normalizer_centralizer_ch6 hBS hb⟩
  have hTS : T ≤ Subgroup.normalizer (S : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTL ht⟩
  have hTYh : T ≤ Subgroup.normalizer (Yh : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTV ht, le_normalizer_centralizer_ch6 hTS ht⟩
  have hTB : T ≤ Subgroup.normalizer (B : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTL ht, Subgroup.le_normalizer (hTS ht)⟩
  have hSn : (S.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr hBS
  have hS2 : IsPGroup 2 ↥(S.subgroupOf B) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSB).symm
  have hidx : ¬ 2 ∣ (S.subgroupOf B).index := by
    intro h2
    apply hS.2.2
    have e := Subgroup.relIndex_mul_relIndex S B L hSB hBL
    have h3 : 2 ∣ S.relIndex L := by rw [← e]; exact Dvd.dvd.mul_right h2 _
    exact h3
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥(S.subgroupOf B)) (S.subgroupOf B).index := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr
      (Nat.two_dvd_ne_zero.mp hidx)))
  obtain ⟨D', hD'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set D := D'.map B.subtype with hDdef
  have hDB : D ≤ B := Subgroup.map_subtype_le D'
  have hDodd : Odd (Nat.card D) := by
    rw [hDdef, Subgroup.card_map_of_injective B.subtype_injective, ← hD'.symm.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hidx)
  have hdec : ∀ b ∈ B, ∃ s ∈ S, ∃ d ∈ D, b = s * d := by
    intro b hb
    obtain ⟨⟨⟨n', hn'⟩, ⟨d, hd⟩⟩, hnd⟩ := hD'.2 ⟨b, hb⟩
    refine ⟨(n' : G), Subgroup.mem_subgroupOf.mp hn', (d : G), ⟨d, hd, rfl⟩, ?_⟩
    exact (congrArg Subtype.val hnd).symm
  have : IsMulCommutative ↥Yh := ⟨⟨fun a b => Subtype.ext (hVc a a.2.1 b b.2.1)⟩⟩
  have hcopD := Vol2.Ch10.SecA.commutator_inf_centralizer_eq_bot (W := Yh) (D := D)
    (fun w hw => hV2 w hw.1) hDodd (hDB.trans hBYh)
  set E := ⁅Yh, B⁆ with hEdef
  have hED : E ≤ ⁅Yh, D⁆ := by
    rw [hEdef, Subgroup.commutator_le]
    intro y hy b hb
    obtain ⟨s, hs, d, hd, rfl⟩ := hdec b hb
    have hdy : d * y⁻¹ * d⁻¹ ∈ Yh :=
      (Subgroup.mem_normalizer_iff.mp (hBYh (hDB hd)) y⁻¹).mp (Yh.inv_mem hy)
    have hsc : s * (d * y⁻¹ * d⁻¹) = (d * y⁻¹ * d⁻¹) * s :=
      Subgroup.mem_centralizer_iff.mp hdy.2 s hs
    have e : ⁅y, s * d⁆ = ⁅y, d⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc y * (s * d) * y⁻¹ * (s * d)⁻¹ = y * (s * (d * y⁻¹ * d⁻¹)) * s⁻¹ := by group
        _ = y * ((d * y⁻¹ * d⁻¹) * s) * s⁻¹ := by rw [hsc]
        _ = y * d * y⁻¹ * d⁻¹ := by group
    rw [e]
    exact Subgroup.commutator_mem_commutator hy hd
  have hEYh : E ≤ Yh := Subgroup.le_normalizer_iff_commutator_le_left.mp hBYh
  have hETn : T ≤ Subgroup.normalizer (E : Set G) := le_normalizer_commutator_ch6 hTYh hTB
  have hET : E ≤ T := hEYh.trans (inf_le_left.trans hVT)
  have hEne : E ≠ ⊥ := by
    intro hE
    have hm : ⁅(w₀ : G), (l : G)⁆ ∈ E := Subgroup.commutator_mem_commutator ⟨w₀.2, hw₀S⟩ hlB
    rw [hE, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
    exact hlw₀ hm.symm
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (E.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hETn
  have hne : E.subgroupOf T ≠ ⊥ := by
    intro h0
    apply hEne
    rw [← Subgroup.map_subgroupOf_eq_of_le hET, h0, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyE : (y : G) ∈ E := hy.1
  have hyC : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  refine ⟨y, (hEYh hyE).1, hyC, fun hyL => hy1 ?_⟩
  have hyD : (y : G) ∈ Subgroup.centralizer (D : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hDB.trans hBL)) hyL
  have h0 : (y : G) ∈ ⁅Yh, D⁆ ⊓ Subgroup.centralizer (D : Set G) := ⟨hED hyE, hyD⟩
  rw [hcopD, Subgroup.mem_bot] at h0
  exact Subtype.ext (Subtype.ext h0)

theorem sl2_mul_self_eq_one_ch6 {K : Type} [Field K] [CharP K 2]
    {A : Matrix (Fin 2) (Fin 2) K} (hdet : A.det = 1) {x : Fin 2 → K} (hx : x ≠ 0)
    (hAx : A.mulVec x = x) : A * A = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : (A - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨x, hx, by rw [Matrix.sub_mulVec, hAx, Matrix.one_mulVec, sub_self]⟩
  rw [Matrix.det_fin_two] at hdet h1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at h1
  have hsum : A 0 0 + A 1 1 = 0 := by linear_combination -h1 + hdet + h2
  have e00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by
    linear_combination -hdet + A 0 0 * hsum - h2
  have e01 : A 0 0 * A 0 1 + A 0 1 * A 1 1 = 0 := by linear_combination A 0 1 * hsum
  have e10 : A 1 0 * A 0 0 + A 1 1 * A 1 0 = 0 := by linear_combination A 1 0 * hsum
  have e11 : A 1 0 * A 0 1 + A 1 1 * A 1 1 = 1 := by
    linear_combination -hdet + A 1 1 * hsum - h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11]

theorem IsNatQuotCh5.mem_centralizer_of_odd_ch6 [Finite G] {S L V : Subgroup G} {n : ℕ}
    (h : IsNatQuotCh5 L V n) (hS : IsSylowTwoOf S L) {d : G} (hdL : d ∈ L)
    (hodd : Odd (orderOf d)) (hdV : d ∉ Subgroup.centralizer (V : Set G)) {v : G} (hv : v ∈ V)
    (hdv : d * v * d⁻¹ = v) : v ∈ Subgroup.centralizer (L : Set G) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.1
  obtain ⟨F, _, _, _, -, ψ, Y, -, hYk, hYe, -⟩ := h.exists_sylowCoord hS
  by_contra hvL
  set a : ↥(autOn L V) := ⟨A4.actionOn V L hLV ⟨d, hdL⟩,
    (A4.mem_autOn_iff hLV).mpr ⟨⟨d, hdL⟩, rfl⟩⟩ with ha
  have hfix : (a : MulAut ↥V) ⟨v, hv⟩ = ⟨v, hv⟩ := Subtype.ext hdv
  have hYv : Multiplicative.toAdd (Y ⟨v, hv⟩) ≠ 0 := by
    intro h0
    apply hvL
    apply (hYk ⟨v, hv⟩).mp
    exact Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
  have hmv := hYe a ⟨v, hv⟩
  rw [hfix] at hmv
  have hsq := sl2_mul_self_eq_one_ch6 (ψ a).2 hYv hmv.symm
  have haa : a * a = 1 := ψ.injective (by
    rw [map_mul, map_one]
    exact Subtype.ext hsq)
  have hd2 : d * d ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have e := congrArg (fun x : ↥(autOn L V) => (((x : MulAut ↥V) ⟨w, hw⟩ : ↥V) : G)) haa
    simp only [ha, Subgroup.coe_mul, MulAut.mul_apply, Subgroup.coe_one, MulAut.one_apply,
      A4.actionOn_apply_coe] at e
    calc w * (d * d) = (d * (d * w * d⁻¹) * d⁻¹) * (d * d) := by rw [e]
      _ = d * d * w := by group
  apply hdV
  obtain ⟨k, hk⟩ := hodd
  have hd : d = (d * d) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf d + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [hd]
  exact Subgroup.pow_mem _ hd2 _

theorem IsNatQuotCh5.mem_of_fixed_ch6 [Finite G] {S L V : Subgroup G} {n : ℕ}
    (h : IsNatQuotCh5 L V n) (hS : IsSylowTwoOf S L)
    (hCL : L ⊓ Subgroup.centralizer (V : Set G) ≤ S) {z : G} (hzV : z ∈ V)
    (hzS : z ∈ Subgroup.centralizer (S : Set G)) (hzL : z ∉ Subgroup.centralizer (L : Set G))
    {l : G} (hl : l ∈ L) (hlz : l * z * l⁻¹ = z) : l ∈ S := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.1
  have hSL : S ≤ L := hS.1
  have hSV : S ≤ Subgroup.normalizer (V : Set G) := hSL.trans hLV
  obtain ⟨F, _, _, _, -, ψ, Y, -, hYk, hYe, hYS⟩ := h.exists_sylowCoord hS
  obtain ⟨s₁, hs₁⟩ := (A4.mem_autOn_iff hSV).mp
    ((hYS (ψ.symm (unipSL 1))).mpr ⟨1, ψ.apply_symm_apply _⟩)
  have hz1 : Multiplicative.toAdd (Y ⟨z, hzV⟩) 1 = 0 := by
    have hfix : ((ψ.symm (unipSL 1) : ↥(autOn L V)) : MulAut ↥V) ⟨z, hzV⟩ = ⟨z, hzV⟩ := by
      rw [← hs₁]
      apply Subtype.ext
      rw [A4.actionOn_apply_coe]
      rw [Subgroup.mem_centralizer_iff.mp hzS s₁ s₁.2, mul_inv_cancel_right]
    have e := hYe (ψ.symm (unipSL 1)) ⟨z, hzV⟩
    rw [hfix, MulEquiv.apply_symm_apply, coe_unipSL, unipSL_mulVec] at e
    have e0 := congrFun e 0
    simp only [Fin.isValue, Matrix.cons_val_zero, one_mul] at e0
    linear_combination -e0
  have hz0 : Multiplicative.toAdd (Y ⟨z, hzV⟩) 0 ≠ 0 := by
    intro h0
    apply hzL
    apply (hYk ⟨z, hzV⟩).mp
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i
    · simpa using h0
    · simpa using hz1
  set a : ↥(autOn L V) := ⟨A4.actionOn V L hLV ⟨l, hl⟩,
    (A4.mem_autOn_iff hLV).mpr ⟨⟨l, hl⟩, rfl⟩⟩ with ha
  have hfix : (a : MulAut ↥V) ⟨z, hzV⟩ = ⟨z, hzV⟩ := Subtype.ext hlz
  have e := hYe a ⟨z, hzV⟩
  rw [hfix] at e
  set g := ψ a with hg
  have e0 := congrFun e 0
  have e1 := congrFun e 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.isValue, hz1, mul_zero,
    add_zero] at e0 e1
  have hg00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have : ((g : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) * Multiplicative.toAdd (Y ⟨z, hzV⟩) 0 = 0 := by
      linear_combination e0.symm
    rcases mul_eq_zero.mp this with h0 | h0
    · linear_combination h0
    · exact absurd h0 hz0
  have hg10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rcases mul_eq_zero.mp e1.symm with h0 | h0
    · exact h0
    · exact absurd h0 hz0
  have hdet := g.2
  rw [Matrix.det_fin_two, hg00, hg10, mul_zero, sub_zero, one_mul] at hdet
  have hgu : g = unipSL ((g : Matrix (Fin 2) (Fin 2) F) 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_unipSL, hg00, hg10, hdet]
  obtain ⟨s, hs⟩ := (A4.mem_autOn_iff hSV).mp ((hYS a).mpr ⟨_, hgu⟩)
  have hc : (s : G)⁻¹ * l ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.inv_mem (hSL s.2)) hl, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have e : (s : G) * v * (s : G)⁻¹ = l * v * l⁻¹ :=
      congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hs
    calc v * ((s : G)⁻¹ * l) = (s : G)⁻¹ * ((s : G) * v * (s : G)⁻¹) * l := by group
      _ = (s : G)⁻¹ * (l * v * l⁻¹) * l := by rw [e]
      _ = (s : G)⁻¹ * l * v := by group
  have e' : l = s * ((s : G)⁻¹ * l) := by group
  rw [e']
  exact S.mul_mem s.2 (hCL hc)

end CFSG.Quasithin.H13
