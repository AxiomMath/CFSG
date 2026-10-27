module

public import CFSG.RankThree.GF2n.Stroth80.Sec57Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec57Y
public import CFSG.RankThree.GF2n.Stroth80.Sec57D
public import CFSG.RankThree.GF2n.Stroth80.Sec57T
import CFSG.RankThree.GF2n.Stroth80.Sec34Symm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_conj_eq_mul_of_not_caseA (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (hB : ¬ CaseA Q Z t) {u : G} (hu : u ∈ Ut Q Z t) : ∃ y ∈ Q, y * t * y⁻¹ = t * u := by
  have hUt : Ut Q Z t⁻¹ = Ut Q Z t := by
    unfold Ut
    rw [Subgroup.zpowers_inv]
  have hinv : t⁻¹ ∈ LB M Q B := (LB M Q B).inv_mem ht
  have hu' : u⁻¹ ∈ Ut Q Z t⁻¹ := by
    rw [hUt]
    exact (Ut Q Z t).inv_mem hu
  obtain ⟨x, hxQ, hcZ⟩ := hc.exists_comm_mul_inv_mem_Z hinv hu'
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = ⁅x, t⁻¹⁆ * (u⁻¹)⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hcZ
  have key : x * t * x⁻¹ = t * u * c⁻¹ := by
    rw [hcdef, commutatorElement_def]
    group
  have hcZ' : c ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
    rw [← cen_eq Q, ← hc.hyp.hZ]
    exact hcZ
  have hcx : x * c = c * x := Subgroup.mem_centralizer_iff.mp hcZ'.2 x hxQ
  have hxcx : x * c * x⁻¹ = c := by
    rw [hcx]
    group
  unfold CaseA at hB
  have hB' : ∀ z ∈ Z, ∃ y ∈ Q, y * t * y⁻¹ = t * z := fun z hz => by
    by_contra h
    exact hB ⟨z, hz, fun y hy heq => h ⟨y, hy, heq⟩⟩
  obtain ⟨y', hy'Q, hy'⟩ := hB' c hcZ
  refine ⟨x * y', Q.mul_mem hxQ hy'Q, ?_⟩
  calc x * y' * t * (x * y')⁻¹ = x * (y' * t * y'⁻¹) * x⁻¹ := by group
    _ = x * (t * c) * x⁻¹ := by rw [hy']
    _ = x * t * x⁻¹ * (x * c * x⁻¹) := by group
    _ = x * t * x⁻¹ * c := by rw [hxcx]
    _ = t * u * c⁻¹ * c := by rw [key]
    _ = t * u := by group

theorem Ctx.conj_mem_Ut (hc : Ctx M Q Z B) {t m : G} (hmM : m ∈ M) (hmt : m * t = t * m)
    {u : G} (hu : u ∈ Ut Q Z t) : m * u * m⁻¹ ∈ Ut Q Z t := by
  have hle : Ut Q Z t ≤ (Ut Q Z t).comap (MulAut.conj m).toMonoidHom := by
    refine sup_le (Subgroup.commutator_le.mpr fun x hx s hs => ?_) fun z hz => ?_
    · have hms : m * s * m⁻¹ = s := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
        have hc2 : Commute m (t ^ k) := Commute.zpow_right (show Commute m t from hmt) k
        rw [hc2.eq, mul_inv_cancel_right]
      have hcon : m * ⁅x, s⁆ * m⁻¹ = ⁅m * x * m⁻¹, m * s * m⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      have hmxQ : m * x * m⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hmM) x).mp hx
      rw [Subgroup.mem_comap]
      show m * ⁅x, s⁆ * m⁻¹ ∈ Ut Q Z t
      rw [hcon, hms]
      exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hmxQ hs)
    · rw [Subgroup.mem_comap]
      show m * z * m⁻¹ ∈ Ut Q Z t
      exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hmM) z).mp hz)
  exact hle hu

theorem Ctx.card_le_inf_M_mul (hc : Ctx M Q Z B) {A : Subgroup G} (hA : A ≤ QB B) :
    Nat.card A ≤ Nat.card ↥(A ⊓ M) * Nat.card Z := by
  have hi : M.relIndex (QB B) * Nat.card ↥(QB B ⊓ M) = Nat.card ↥(QB B) := by
    rw [inf_comm (QB B) M]
    exact Subgroup.relIndex_mul_card M (QB B)
  have hc2 : Nat.card ↥(QB B) = Nat.card ↥(QB B ⊓ M) * Nat.card Z := by
    rw [hc.card_QB_eq, hc.QB_inf_M_eq]
  have hpos : 0 < Nat.card ↥(QB B ⊓ M) := Nat.card_pos
  have hZ : M.relIndex (QB B) = Nat.card Z := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hi, hc2]
    exact Nat.mul_comm _ _
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hne : M.relIndex (QB B) ≠ 0 := by
    rw [hZ]
    exact hZpos.ne'
  have hle : M.relIndex A ≤ M.relIndex (QB B) := Subgroup.relIndex_le_of_le_right hA hne
  have h5 : M.relIndex A * Nat.card ↥(A ⊓ M) = Nat.card ↥A := by
    rw [inf_comm A M]
    exact Subgroup.relIndex_mul_card M A
  calc Nat.card A = M.relIndex A * Nat.card ↥(A ⊓ M) := h5.symm
    _ ≤ Nat.card Z * Nat.card ↥(A ⊓ M) := Nat.mul_le_mul (hle.trans hZ.le) le_rfl
    _ = Nat.card ↥(A ⊓ M) * Nat.card Z := Nat.mul_comm _ _

theorem Ctx.card_QB_inf_QB (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hRT : RootTrans M Q Z B) {Y : Subgroup G} {h : G} (hY : Y = conjSubgroup h Z)
    (hYB : Y ≠ B) (hBY : B ≤ QB Y) :
    Nat.card ↥(QB B ⊓ QB Y) = Nat.card Z ^ (n + 1) := by
  obtain ⟨g, hg⟩ := hc.conj
  have hYQB : Y ≤ QB B := hc.hyp.le_QB_of_le_QB ⟨g, hg⟩ ⟨h, hY⟩ (Ne.symm hYB) hBY
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  have hgQB : conjSubgroup g⁻¹ (QB B) = Q := by
    rw [hQB, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hY'Q : conjSubgroup g⁻¹ Y ≤ Q := by
    have h1 : conjSubgroup g⁻¹ Y ≤ conjSubgroup g⁻¹ (QB B) := Subgroup.map_mono hYQB
    exact h1.trans hgQB.le
  have hY'eq : conjSubgroup g⁻¹ Y = conjSubgroup (g⁻¹ * h) Z := by
    rw [hY, conjSubgroup_conjSubgroup]
  have hY'Z : conjSubgroup g⁻¹ Y ≠ Z := by
    intro hZ
    apply hYB
    have e : conjSubgroup g (conjSubgroup g⁻¹ Y) = Y := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    exact e.symm.trans ((congrArg (conjSubgroup g) hZ).trans hg.symm)
  have hY' : Ctx M Q Z (conjSubgroup g⁻¹ Y) :=
    { hyp := hc.hyp
      conj := ⟨g⁻¹ * h, hY'eq⟩
      le := hY'Q
      ne := hY'Z }
  obtain ⟨m, hmM, hm⟩ := hRT (conjSubgroup g⁻¹ Y) hY'
  have hmQB : conjSubgroup m (QB B) = conjSubgroup g⁻¹ (QB Y) := by
    rw [← QB_conj m B, hm, QB_conj g⁻¹ Y]
  have key : conjSubgroup g⁻¹ (QB B ⊓ QB Y) = conjSubgroup m (Q ⊓ QB B) := by
    rw [conjSubgroup_inf, conjSubgroup_inf, hgQB, hc.conj_Q_eq hmM, hmQB]
  have hcard : Nat.card ↥(Q ⊓ QB B) = Nat.card ↥(QB B ⊓ QB Y) := by
    have h1 := card_conjSubgroup g⁻¹ (QB B ⊓ QB Y)
    rw [key, card_conjSubgroup] at h1
    exact h1
  exact hcard.symm.trans (stroth_3_5 h34 hc hw hn hno hgen).2.2.2

theorem Ctx.pow_le_card_Lambda (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hRT : RootTrans M Q Z B) {Y : Subgroup G} {h : G} (hY : Y = conjSubgroup h Z)
    (hYB : Y ≠ B) (hBY : B ≤ QB Y) :
    Nat.card Z ^ n ≤ Nat.card ↥(QB B ⊓ QB Y ⊓ M) := by
  have h1 := hc.card_le_inf_M_mul (A := QB B ⊓ QB Y) inf_le_left
  have h2 := Ctx.card_QB_inf_QB h34 hc hw hn hno hgen hRT hY hYB hBY
  rw [h2, pow_succ] at h1
  exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos

theorem Ctx.inf_Lambda_Q (hc : Ctx M Q Z B) {Y : Subgroup G} :
    (QB B ⊓ QB Y ⊓ M) ⊓ Q = Q ⊓ QB Y ⊓ QB B := by
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨⟨hB, hY⟩, -⟩, hQ⟩
    exact ⟨⟨hQ, hY⟩, hB⟩
  · rintro ⟨⟨hQ, hY⟩, hB⟩
    exact ⟨⟨⟨hB, hY⟩, hc.hyp.Q_normal.1 hQ⟩, hQ⟩

theorem Ctx.W_le_Vt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {Y : Subgroup G}
    (hs : Sit M Q Z Y t) (hRT : RootTrans M Q Z B)
    (hB0 : ∀ u ∈ Ut Q Z t, ∃ y ∈ Q, y * t * y⁻¹ = t * u) :
    Q ⊓ QB Y ⊓ Ut Q Z t ≤ Vt M (LB M Q B) B Z t := by
  have H := hc.hyp
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨kY, hkY, hQBY, -⟩ := hs.QB_eq
  have h12 := smith_1_12 hs
  have hZQ : Z ⊓ QB Y = ⊥ := Z_inf_QB_eq_bot hs h12
  rintro α ⟨⟨hαQ, hαY⟩, hαU⟩
  by_cases hα1 : α = 1
  · rw [hα1]; exact (Vt M (LB M Q B) B Z t).one_mem
  have hαZ : α ∉ Z := fun hZ => hα1 (by
    have : α ∈ Z ⊓ QB Y := ⟨hZ, hαY⟩
    rwa [hZQ, Subgroup.mem_bot] at this)
  have hαYn : α ∉ Y := fun hY => hα1 (by
    have : α ∈ Y ⊓ Q := ⟨hY, hαQ⟩
    rwa [h12.2, Subgroup.mem_bot] at this)
  have hα'Q : kY⁻¹ * α * kY ∈ Q := by
    have h1 : α ∈ QB Y := hαY
    rw [hQBY, mem_conjSubgroup] at h1
    exact h1
  have hα'Z : kY⁻¹ * α * kY ∉ Z := fun hZ => hαYn (by
    rw [hkY]; exact mem_conjSubgroup.mpr hZ)
  have ht'Z : kY⁻¹ * t * kY ∈ Z := by
    have := hs.mem
    rw [hkY, mem_conjSubgroup] at this
    exact this
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨q, hqQ, hq⟩ := GM.exists_comm hD hα'Q hα'Z ht'Z
  have hconj1 : (kY * q * kY⁻¹) * α * (kY * q * kY⁻¹)⁻¹ = t⁻¹ * α := by
    have h1 : q * (kY⁻¹ * α * kY) * q⁻¹ = (kY⁻¹ * t * kY)⁻¹ * (kY⁻¹ * α * kY) := by
      rw [← hq]; simp only [commutatorElement_def]; group
    calc (kY * q * kY⁻¹) * α * (kY * q * kY⁻¹)⁻¹
        = kY * (q * (kY⁻¹ * α * kY) * q⁻¹) * kY⁻¹ := by group
      _ = t⁻¹ * α := by rw [h1]; group
  obtain ⟨y, hyQ, hy⟩ := hB0 α hαU
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hs.x_sq
  have hroot : ∃ (h' z : G), z ∈ Z ∧ α = h' * z * h'⁻¹ := by
    refine ⟨(kY * q * kY⁻¹)⁻¹ * y * kY, kY⁻¹ * t * kY, ht'Z, ?_⟩
    calc α = (kY * q * kY⁻¹)⁻¹ * ((kY * q * kY⁻¹) * α * (kY * q * kY⁻¹)⁻¹) *
          (kY * q * kY⁻¹) := by group
      _ = (kY * q * kY⁻¹)⁻¹ * (t⁻¹ * α) * (kY * q * kY⁻¹) := by rw [hconj1]
      _ = (kY * q * kY⁻¹)⁻¹ * (y * t * y⁻¹) * (kY * q * kY⁻¹) := by rw [htinv, hy]
      _ = _ := by group
  obtain ⟨h', z, hzZ, hαeq⟩ := hroot
  obtain ⟨g', hg'Q, hαg'⟩ := stroth_2_6 H hαQ hαZ ⟨h', z, hzZ, hαeq⟩
  obtain ⟨g'', hg''Q, hαg''⟩ := stroth_2_6 H hα'Q hα'Z
    ⟨kY⁻¹ * h', z, hzZ, by rw [hαeq]; group⟩
  have hαkg'' : α ∈ conjSubgroup (kY * g'') Z := by
    rw [mem_conjSubgroup]
    have e : (kY * g'')⁻¹ * α * (kY * g'') = g''⁻¹ * (kY⁻¹ * α * kY) * g'' := by group
    rw [e]
    exact mem_conjSubgroup.mp hαg''
  have hBαeq : conjSubgroup g' Z = conjSubgroup (kY * g'') Z :=
    conjSubgroup_eq_of_mem_ne_one H hα1 hαg' hαkg''
  have hBαY : conjSubgroup g' Z ≤ QB Y := by
    rw [hBαeq, conjSubgroup_mul, hQBY]
    exact Subgroup.map_mono hg''Q
  have hBαne_Z : conjSubgroup g' Z ≠ Z := fun e => hαZ (by rw [← e]; exact hαg')
  have hBαY' : conjSubgroup g' Z ≠ Y := fun e => hαYn (by rw [← e]; exact hαg')
  have hYle : Y ≤ QB (conjSubgroup g' Z) :=
    H.le_QB_of_le_QB ⟨g', rfl⟩ ⟨kY, hkY⟩ hBαY' hBαY
  have htLB : t ∈ LB M Q (conjSubgroup g' Z) := Subgroup.mem_sup_right ⟨hYle hs.mem, htM⟩
  have hcα : Ctx M Q Z (conjSubgroup g' Z) := ⟨H, ⟨g', rfl⟩, hg'Q, hBαne_Z⟩
  obtain ⟨m, hm, hmB⟩ := hRT _ hcα
  have htm : t ∈ conjSubgroup m (LB M Q B) := by
    rw [← hc.LB_conj hm, hmB]
    exact htLB
  exact sec39_conjB_le_Vt hm htm (by rw [hmB]; exact hαg')

theorem Ctx.comm_Ut_QB_mem (hc : Ctx M Q Z B) {t : G} {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hUc : Ut Q Z t ≤ Subgroup.centralizer ({t} : Set G)) {u l : G} (hu : u ∈ Ut Q Z t)
    (hlY : l ∈ QB Y) (hlM : l ∈ M) : ⁅u, l⁆ ∈ Q ⊓ QB Y ⊓ Ut Q Z t := by
  have htM : t ∈ M := hs.memM
  have huQ : u ∈ Q := hc.Ut_le_Q htM hu
  have hluQ : l * u⁻¹ * l⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) u⁻¹).mp (Q.inv_mem huQ)
  have hcomm : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by
    simp only [commutatorElement_def]
    group
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hcomm]
    exact Q.mul_mem huQ hluQ
  · have hut : u * t = t * u := Subgroup.mem_centralizer_singleton_iff.mp (hUc hu)
    have hun : u ∈ Subgroup.normalizer (Y : Set G) := mem_normalizer_of_comm_Y hs hut
    have h1 : u * l * u⁻¹ ∈ QB Y := hs.normalizer_QB hun hlY
    rw [show ⁅u, l⁆ = (u * l * u⁻¹) * l⁻¹ by rw [commutatorElement_def]]
    exact (QB Y).mul_mem h1 ((QB Y).inv_mem hlY)
  · have hlt : l * t = t * l := (hs.QB_comm_X hs.mem hlY).symm
    have h1 := hc.conj_mem_Ut hlM hlt hu
    rw [hcomm]
    refine (Ut Q Z t).mul_mem hu ?_
    have h2 := (Ut Q Z t).inv_mem h1
    rwa [show (l * u * l⁻¹)⁻¹ = l * u⁻¹ * l⁻¹ by group] at h2

theorem Ctx.Vt_le_inf_QB_of_SLNat (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) (hsl : SLNat hc t) :
    Vt M (LB M Q B) B Z t ≤ Q ⊓ QB B := by
  have htm : t ∈ conjSubgroup 1 (LB M Q B) := by
    rw [conjSubgroup_one]
    exact hs.mem
  have h1 := hc.Tt_comm_le_inf_QB hs.mem M.one_mem htm
  rw [conjSubgroup_one] at h1
  exact (hc.Vt_le_Tt_of_SLNat hs h35 hsl).trans
    (sup_le h1 (le_inf hc.Z_le_Q hc.Z_le_QB.1))

theorem stroth310SL_of_34 (h34 : Stroth34Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec5Hyp hc n t → SLNat hc t → Vt M (LB M Q B) B Z t ≤ QB B := by
  intro G _ _ M Q Z B hc n t hs hsl
  exact (hc.Vt_le_inf_QB_of_SLNat hs (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
    hsl).trans inf_le_right

theorem stroth_5_7_caseB_core (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (h : Sec5Hyp hc n t) (hRT : RootTrans M Q Z B) (hSL : SLNat hc t) {Y : Subgroup G}
    (hs : Sit M Q Z Y t) (hBY : B ≤ QB Y) (hB : ¬ CaseA Q Z t) :
    Vt M (LB M Q B) B Z t ≤ (Q ⊓ QB Y) ⊔ Z := by
  have H := hc.hyp
  have ht := h.mem
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨kY, hkY, -, -⟩ := hs.QB_eq
  obtain ⟨g, hg⟩ := hc.conj
  have h12 := smith_1_12 hs
  have hZY : Z ⊓ QB Y = ⊥ := Z_inf_QB_eq_bot hs h12
  have ht2 : t ^ 2 = 1 := by
    rw [sq]
    exact hs.x_sq
  have hUc : Ut Q Z t ≤ Subgroup.centralizer ({t} : Set G) := hc.Ut_le_centralizer h34 h hSL ht2
  have hYB : Y ≠ B := fun e => h.notQ (hc.le (e ▸ hs.mem))
  have hBY' : ∀ x ∈ B, x ∈ Y → x = 1 := fun x hxB hxY => by
    by_contra hx1
    apply hYB
    have h1 : x ∈ conjSubgroup kY Z := hkY ▸ hxY
    have h2 : x ∈ conjSubgroup g Z := hg ▸ hxB
    rw [hkY, hg]
    exact conjSubgroup_eq_of_mem_ne_one H hx1 h1 h2
  have hW : Q ⊓ QB Y ⊓ Ut Q Z t ≤ Vt M (LB M Q B) B Z t :=
    hc.W_le_Vt ht hs hRT fun u hu => hc.exists_conj_eq_mul_of_not_caseA ht hB hu
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := by
    have := conjSubgroup_le_Rt (M := M) (L := LB M Q B) (t := t) M.one_mem
      (by rw [conjSubgroup_one]; exact ht)
    rwa [conjSubgroup_one] at this
  have hΛCN : ∀ l ∈ QB B ⊓ QB Y ⊓ M, l ∈ hc.CN t := fun l hl =>
    hc.mem_CN_of_comm_Ut_le_Vt h34 h hSL (hLR (Subgroup.mem_sup_right ⟨hl.1.1, hl.2⟩))
      fun u hu => hW (hc.comm_Ut_QB_mem hs hUc hu hl.1.2 hl.2)
  have hΛle : QB B ⊓ QB Y ⊓ M ≤ QB B ⊓ M := fun l hl => ⟨hl.1.1, hl.2⟩
  have hAle : Q ⊓ QB Y ⊓ QB B ≤ Q ⊓ QB B := fun a ha => ⟨ha.1.1, ha.2⟩
  have hAZ : (Q ⊓ QB Y ⊓ QB B) ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ Z ⊓ QB Y := ⟨hx.2, hx.1.1.2⟩
    rwa [hZY] at this
  have hcommΛA : ∀ l ∈ QB B ⊓ QB Y ⊓ M, ∀ a ∈ Q ⊓ QB Y ⊓ QB B, ⁅l, a⁆ = 1 := fun l hl a ha =>
    hBY' _ (hc.comm_QB_le_B hl.1.1 ha.2) (hs.comm_QB_mem_X hl.1.2 ha.1.2)
  have hcard : Nat.card Z ^ n * Nat.card ↥((QB B ⊓ QB Y ⊓ M) ⊓ Q) ≤
      Nat.card ↥(Q ⊓ QB Y ⊓ QB B) * Nat.card ↥(QB B ⊓ QB Y ⊓ M) := by
    rw [hc.inf_Lambda_Q, Nat.mul_comm (Nat.card ↥(Q ⊓ QB Y ⊓ QB B))]
    exact Nat.mul_le_mul_right _
      (hc.pow_le_card_Lambda h34 h.width h.n_gt h.noA2 h.gen hRT hkY hYB hBY)
  intro v hv
  have hvA := hc.pairing_count h34 h hΛle hAle hAZ hcommΛA hcard v
    (hc.Vt_le_inf_QB_of_SLNat h (stroth_3_5 h34 hc h.width h.n_gt h.noA2 h.gen).2.1 hSL hv)
    fun l hl => (hΛCN l hl).2 v hv
  exact (sup_le_sup_right (fun x hx => ⟨hx.1.1, hx.1.2⟩) Z) hvA

theorem stroth_5_7_caseB (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (h : Sec5Hyp hc n t) (hRT : RootTrans M Q Z B) (hSL : SLNat hc t)
    (hb : ∃ g : G, ∃ b ∈ B, g * t * g⁻¹ = b) (hBt : B ≤ QB (Subgroup.zpowers t))
    (hB : ¬ CaseA Q Z t) :
    Vt M (LB M Q B) B Z t ≤ (Q ⊓ QB (Subgroup.zpowers t)) ⊔ Z := by
  obtain ⟨Y, -, -, -, hs⟩ := h.exists_root hc hb
  have hBY : B ≤ QB Y := root_le_QB_of_le_QB_zpowers hs hc.conj hBt
  exact (stroth_5_7_caseB_core h34 hc h hRT hSL hs hBY hB).trans
    (sup_le_sup_right (inf_le_inf_left Q (QB_le_QB_zpowers hs)) Z)

end CFSG.RankThree.GF2n.Stroth80
