module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517A5Split

public section

namespace CFSG.Quasithin.H13.A5Push

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin Equiv

theorem d5_comm_rel : ∀ α ∈ e4List, ∀ β ∈ e4List, ∀ x z : Fin 5 → ZMod 2,
    pmv α x = x → pmv β z = z → pmv β⁻¹ x + x = pmv α⁻¹ z + z → pmv β⁻¹ x + x = 0 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_of_mul_self {a y : G} (ha : a * a = 1) (hy : y * y = 1)
    (h : a * y * (a * y) = 1) : y * a = a * y := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  calc y * a = a⁻¹ * (a * y * (a * y)) * y⁻¹ := by group
    _ = a⁻¹ * 1 * y⁻¹ := by rw [h]
    _ = a * y := by rw [ha', hy']; group

namespace Setting

variable {T M L W : Subgroup G} {F : S5Frame (L ⊔ T) W} {n : ℕ}

structure Partner (hs : Setting T M L W F n) (P : Subgroup G) : Prop where
  elQ : IsElemAbelian 2 (baum T ⊓ Subgroup.centralizer (W : Set G))
  maxP : IsMaxElemAbelian T P
  sup : (baum T ⊓ Subgroup.centralizer (W : Set G)) ⊔ P = baum T
  QC_le : baum T ⊓ Subgroup.centralizer (L : Set G) ≤ P

variable {hs : Setting T M L W F n} {P : Subgroup G}

omit [Finite G] in
theorem le_S_of_isMax {A : Subgroup G} (hA : IsMaxElemAbelian T A) : A ≤ baum T :=
  (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ T).trans (B2F.thompsonJ_le_baum T)

theorem Partner.P_le (hp : hs.Partner P) : P ≤ baum T := le_S_of_isMax hp.maxP

theorem Partner.QC_central (hp : hs.Partner P) {c : G}
    (hc : c ∈ baum T ⊓ Subgroup.centralizer (L : Set G)) {s : G} (hsS : s ∈ baum T) :
    s * c = c * s := by
  have hcQ : c ∈ Subgroup.centralizer ((baum T ⊓ Subgroup.centralizer (W : Set G) :
      Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := hp.elQ.1
    exact setLike_mul_comm hq (hs.QC_le_Q hc)
  have hcP : c ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := hp.maxP.2.1.1
    exact setLike_mul_comm hq (hp.QC_le hc)
  have h1 := mem_centralizer_sup hcQ hcP
  rw [hp.sup] at h1
  exact Subgroup.mem_centralizer_iff.mp h1 s hsS

omit [Finite G] in
theorem rel_of_commute {a b y z : G} (hab : a * b = b * a) (h : a * y * (b * z) = b * z * (a * y))
    (hyz : y * z = z * y) : b⁻¹ * y * b * y⁻¹ = a⁻¹ * z * a * z⁻¹ := by
  have hba : b⁻¹ * a⁻¹ * b = a⁻¹ := by
    have h1 : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hab]
    rw [h1]
    group
  have h2 : b⁻¹ * y * b * z = a⁻¹ * z * a * y := by
    calc b⁻¹ * y * b * z = b⁻¹ * a⁻¹ * (a * y * (b * z)) := by group
      _ = b⁻¹ * a⁻¹ * (b * z * (a * y)) := by rw [h]
      _ = (b⁻¹ * a⁻¹ * b) * z * a * y := by group
      _ = a⁻¹ * z * a * y := by rw [hba]
  have h3 : y * z⁻¹ * y⁻¹ = z⁻¹ := by
    calc y * z⁻¹ * y⁻¹ = y * (z⁻¹ * y⁻¹) := by group
      _ = y * (y * z)⁻¹ := by rw [mul_inv_rev]
      _ = y * (z * y)⁻¹ := by rw [hyz]
      _ = z⁻¹ := by group
  calc b⁻¹ * y * b * y⁻¹ = (b⁻¹ * y * b * z) * z⁻¹ * y⁻¹ := by group
    _ = (a⁻¹ * z * a * y) * z⁻¹ * y⁻¹ := by rw [h2]
    _ = a⁻¹ * z * a * (y * z⁻¹ * y⁻¹) := by group
    _ = a⁻¹ * z * a * z⁻¹ := by rw [h3]

omit [Finite G] in
theorem _root_.CFSG.Quasithin.H13.S5Frame.c_comm_inv {Y W : Subgroup G} (F : S5Frame Y W)
    (s : ↥Y) (u : ↥W)
    (h : (s : G)⁻¹ * u * s * (u : G)⁻¹ ∈ W) :
    F.c ⟨_, h⟩ = pmv (F.ρ s)⁻¹ (F.c u) + F.c u := by
  have h' : ((s⁻¹ : ↥Y) : G) * u * ((s⁻¹ : ↥Y) : G)⁻¹ * (u : G)⁻¹ ∈ W := by simpa using h
  have e : (⟨_, h⟩ : ↥W) = ⟨_, h'⟩ := Subtype.ext (by simp)
  rw [e, F.c_comm s⁻¹ u h', map_inv]

omit [Finite G] in
theorem _root_.CFSG.Quasithin.H13.S5Frame.commute_of_rel {Y W : Subgroup G} (F : S5Frame Y W)
    (s t : ↥Y) (u v : ↥W)
    (hs : InE4 (F.ρ s)) (ht : InE4 (F.ρ t)) (htu : (t : G) * u = u * t)
    (hsv : (s : G) * v = v * s)
    (hrel : (s : G)⁻¹ * u * s * (u : G)⁻¹ = (t : G)⁻¹ * v * t * (v : G)⁻¹) :
    (s : G) * u = u * s := by
  have hx : pmv (F.ρ t) (F.c u) = F.c u :=
    (F.c_conj_eq t u u (by rw [htu, mul_inv_cancel_right])).symm
  have hz : pmv (F.ρ s) (F.c v) = F.c v :=
    (F.c_conj_eq s v v (by rw [hsv, mul_inv_cancel_right])).symm
  have hmem : ∀ (r : ↥Y) (x : ↥W), (r : G)⁻¹ * x * r * (x : G)⁻¹ ∈ W := by
    intro r x
    refine W.mul_mem ?_ (W.inv_mem x.2)
    have := (Subgroup.mem_normalizer_iff.mp (F.le (Y.inv_mem r.2)) x).mp x.2
    simpa using this
  have h1 : F.c ⟨_, hmem s u⟩ = F.c ⟨_, hmem t v⟩ := congrArg F.c (Subtype.ext hrel)
  rw [F.c_comm_inv s u, F.c_comm_inv t v] at h1
  have h2 := d5_comm_rel (F.ρ t) (mem_e4List ht) (F.ρ s) (mem_e4List hs) (F.c u) (F.c v) hx hz h1
  rw [← F.c_comm_inv s u (hmem s u), F.c_eq_zero_iff] at h2
  have h3 : (s : G)⁻¹ * u * s * (u : G)⁻¹ = 1 := congrArg Subtype.val h2
  have h4 : (s : G)⁻¹ * u * s = u := by
    calc (s : G)⁻¹ * u * s = (s : G)⁻¹ * u * s * (u : G)⁻¹ * u := by group
      _ = u := by rw [h3, one_mul]
  calc (s : G) * u = s * ((s : G)⁻¹ * u * s) := by rw [h4]
    _ = u * s := by group

theorem Partner.mem_of_label (hp : hs.Partner P) {A A' : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hA' : IsMaxElemAbelian T A')
    (hlab : ∀ b : ↥(L ⊔ T), (b : G) ∈ A → ∃ b' : ↥(L ⊔ T), (b' : G) ∈ A' ∧ F.ρ b' = F.ρ b)
    (a a' : ↥(L ⊔ T)) (ha : (a : G) ∈ A) (ha' : (a' : G) ∈ A') (haa : F.ρ a' = F.ρ a) :
    (a' : G) ∈ A := by
  classical
  have hAS := le_S_of_isMax hA
  have hA'S := le_S_of_isMax hA'
  have hQmax := hs.isMax_Q hp.elQ
  have hinv : ∀ x : G, ∀ X : Subgroup G, IsMaxElemAbelian T X → x ∈ X → x * x = 1 :=
    fun x X hX hx => by rw [← pow_two]; exact hX.2.1.2 x hx
  have hyS : ((a⁻¹ * a' : ↥(L ⊔ T)) : G) ∈ baum T :=
    (baum T).mul_mem ((baum T).inv_mem (hAS ha)) (hA'S ha')
  have hyQ : ((a⁻¹ * a' : ↥(L ⊔ T)) : G) ∈ baum T ⊓ Subgroup.centralizer (W : Set G) := by
    rw [← hs.rho_eq_one_iff _ hyS, map_mul, map_inv, haa, inv_mul_cancel]
  obtain ⟨y, hyQ', hydef⟩ : ∃ y : G, y ∈ baum T ⊓ Subgroup.centralizer (W : Set G) ∧
      y = ((a⁻¹ * a' : ↥(L ⊔ T)) : G) := ⟨_, hyQ, rfl⟩
  have hay : (a' : G) = a * y := by rw [hydef]; simp
  have hy2 := hinv y _ hQmax hyQ'
  have ha2 := hinv _ A hA ha
  have hya : y * a = a * y :=
    commute_of_mul_self ha2 hy2 (by rw [← hay]; exact hinv _ A' hA' ha')
  have hyA : ∀ b ∈ A, b * y = y * b := by
    intro b hb
    have hbS : b ∈ baum T := hAS hb
    set b₀ : ↥(L ⊔ T) := ⟨b, Subgroup.mem_sup_right (S_le_T T hbS)⟩ with hb₀
    obtain ⟨b', hb'A', hbb⟩ := hlab b₀ hb
    have hzS : ((b₀⁻¹ * b' : ↥(L ⊔ T)) : G) ∈ baum T :=
      (baum T).mul_mem ((baum T).inv_mem hbS) (hA'S hb'A')
    have hzQ : ((b₀⁻¹ * b' : ↥(L ⊔ T)) : G) ∈ baum T ⊓ Subgroup.centralizer (W : Set G) := by
      rw [← hs.rho_eq_one_iff _ hzS, map_mul, map_inv, hbb, inv_mul_cancel]
    obtain ⟨z, hzQ', hzdef⟩ : ∃ z : G, z ∈ baum T ⊓ Subgroup.centralizer (W : Set G) ∧
        z = ((b₀⁻¹ * b' : ↥(L ⊔ T)) : G) := ⟨_, hzQ, rfl⟩
    have hbz : (b' : G) = b * z := by rw [hzdef]; simp [hb₀]
    have hb2 := hinv _ A hA hb
    have hz2 := hinv z _ hQmax hzQ'
    have hzb : z * b = b * z :=
      commute_of_mul_self hb2 hz2 (by rw [← hbz]; exact hinv _ A' hA' hb'A')
    have hab : (a : G) * b = b * a := by
      have := hA.2.1.1
      exact setLike_mul_comm ha hb
    have hab' : (a' : G) * b' = b' * a' := by
      have := hA'.2.1.1
      exact setLike_mul_comm ha' hb'A'
    have hyz : y * z = z * y := by
      have := hp.elQ.1
      exact setLike_mul_comm hyQ' hzQ'
    have hrel := rel_of_commute hab (by rw [← hay, ← hbz]; exact hab') hyz
    obtain ⟨wy, hwy, cy, hcy, rfl⟩ := hs.mem_decomp hyQ'
    obtain ⟨wz, hwz, cz, hcz, rfl⟩ := hs.mem_decomp hzQ'
    have haS : (a : G) ∈ baum T := hAS ha
    have hcya : cy * a = a * cy := (hp.QC_central hcy haS).symm
    have hcyb : cy * b = b * cy := (hp.QC_central hcy hbS).symm
    have hcza : cz * a = a * cz := (hp.QC_central hcz haS).symm
    have hczb : cz * b = b * cz := (hp.QC_central hcz hbS).symm
    have hrel' : b⁻¹ * wy * b * wy⁻¹ = (a : G)⁻¹ * wz * a * wz⁻¹ := by
      have e1 : b⁻¹ * (wy * cy) * b * (wy * cy)⁻¹ = b⁻¹ * wy * b * wy⁻¹ := by
        calc b⁻¹ * (wy * cy) * b * (wy * cy)⁻¹ = b⁻¹ * wy * (cy * b) * cy⁻¹ * wy⁻¹ := by group
          _ = b⁻¹ * wy * (b * cy) * cy⁻¹ * wy⁻¹ := by rw [hcyb]
          _ = b⁻¹ * wy * b * wy⁻¹ := by group
      have e2 : (a : G)⁻¹ * (wz * cz) * a * (wz * cz)⁻¹ = (a : G)⁻¹ * wz * a * wz⁻¹ := by
        calc (a : G)⁻¹ * (wz * cz) * a * (wz * cz)⁻¹ =
            (a : G)⁻¹ * wz * (cz * a) * cz⁻¹ * wz⁻¹ := by group
          _ = (a : G)⁻¹ * wz * (a * cz) * cz⁻¹ * wz⁻¹ := by rw [hcza]
          _ = (a : G)⁻¹ * wz * a * wz⁻¹ := by group
      rw [← e1, ← e2]
      exact hrel
    have hawy : (a : G) * wy = wy * a := by
      have h1 : wy * cy * a = a * (wy * cy) := hya
      calc (a : G) * wy = a * (wy * cy) * cy⁻¹ := by group
        _ = wy * cy * a * cy⁻¹ := by rw [h1]
        _ = wy * (cy * a) * cy⁻¹ := by group
        _ = wy * (a * cy) * cy⁻¹ := by rw [hcya]
        _ = wy * a := by group
    have hbwz : b * wz = wz * b := by
      have h1 : wz * cz * b = b * (wz * cz) := hzb
      calc b * wz = b * (wz * cz) * cz⁻¹ := by group
        _ = wz * cz * b * cz⁻¹ := by rw [h1]
        _ = wz * (cz * b) * cz⁻¹ := by group
        _ = wz * (b * cz) * cz⁻¹ := by rw [hczb]
        _ = wz * b := by group
    have hbwy := F.commute_of_rel b₀ a ⟨wy, hwy⟩ ⟨wz, hwz⟩ (hs.hB.rho_baum b₀ hbS)
      (hs.hB.rho_baum a haS) hawy hbwz hrel'
    calc b * (wy * cy) = b * wy * cy := by group
      _ = wy * b * cy := by rw [show b * wy = wy * b from hbwy]
      _ = wy * (b * cy) := by group
      _ = wy * (cy * b) := by rw [hcyb]
      _ = wy * cy * b := by group
  have hyT : y ∈ T := S_le_T T hyQ'.1
  have hyA' : y ∈ A := mem_of_commute hA hyT hy2 hyA
  rw [hay]
  exact A.mul_mem ha hyA'

theorem Partner.eq_of_label (hp : hs.Partner P) {A A' : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hA' : IsMaxElemAbelian T A')
    (hlab : ∀ b : ↥(L ⊔ T), (b : G) ∈ A → ∃ b' : ↥(L ⊔ T), (b' : G) ∈ A' ∧ F.ρ b' = F.ρ b)
    (hlab' : ∀ b' : ↥(L ⊔ T), (b' : G) ∈ A' → ∃ b : ↥(L ⊔ T), (b : G) ∈ A ∧ F.ρ b = F.ρ b') :
    A = A' := by
  have hle : A' ≤ A := by
    intro x hx
    set x' : ↥(L ⊔ T) := ⟨x, Subgroup.mem_sup_right (S_le_T T (le_S_of_isMax hA' hx))⟩ with hx'
    obtain ⟨b, hbA, hbb⟩ := hlab' x' hx
    exact hp.mem_of_label hA hA' hlab b x' hbA hx hbb.symm
  exact (Subgroup.eq_of_le_of_card_ge hle (hA'.2.2 A hA.1 hA.2.1)).symm

theorem surj_of_sup (hs : Setting T M L W F n) {X : Subgroup G} (hXS : X ≤ baum T)
    (hsup : (baum T ⊓ Subgroup.centralizer (W : Set G)) ⊔ X = baum T) (ε : Perm (Fin 5))
    (hε : InE4 ε) : ∃ x : ↥(L ⊔ T), (x : G) ∈ X ∧ F.ρ x = ε := by
  obtain ⟨s, hsS, hsε⟩ := hs.hB.rho_baum_surj ε hε
  have hXN : X ≤ Subgroup.normalizer
      ((baum T ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) :=
    hXS.trans ((S_le_T T).trans hs.T_le_normalizer_Q)
  have h1 : (s : G) ∈ (((baum T ⊓ Subgroup.centralizer (W : Set G)) ⊔ X : Subgroup G) :
      Set G) := by rw [hsup]; exact hsS
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ X hXN] at h1
  obtain ⟨q, hq, x, hx, hqx⟩ := Set.mem_mul.mp h1
  have hxY : x ∈ L ⊔ T := Subgroup.mem_sup_right (S_le_T T (hXS hx))
  have hqY : q ∈ L ⊔ T := Subgroup.mem_sup_right (S_le_T T hq.1)
  refine ⟨⟨x, hxY⟩, hx, ?_⟩
  have hq1 : F.ρ ⟨q, hqY⟩ = 1 := (hs.rho_eq_one_iff ⟨q, hqY⟩ hq.1).2 hq
  have e : s = ⟨q, hqY⟩ * ⟨x, hxY⟩ := Subtype.ext hqx.symm
  rw [← hsε, e, map_mul, hq1, one_mul]

theorem Partner.eq_P_of_sup (hp : hs.Partner P) {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hsup : (baum T ⊓ Subgroup.centralizer (W : Set G)) ⊔ A = baum T) : A = P := by
  have hAS := le_S_of_isMax hA
  refine hp.eq_of_label hA hp.maxP (fun b hb => ?_) fun b hb => ?_
  · exact surj_of_sup hs hp.P_le hp.sup _ (hs.hB.rho_baum b (hAS hb))
  · exact surj_of_sup hs hAS hsup _ (hs.hB.rho_baum b (hp.P_le hb))

theorem Partner.eq_Q_of_sup (hp : hs.Partner P) {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hsup : P ⊔ A = baum T) : A = baum T ⊓ Subgroup.centralizer (W : Set G) := by
  have hAS := le_S_of_isMax hA
  have hQmax := hs.isMax_Q hp.elQ
  by_cases hAW : A ≤ Subgroup.centralizer (W : Set G)
  · exact Subgroup.eq_of_le_of_card_ge (le_inf hAS hAW) (hA.2.2 _ hQmax.1 hQmax.2.1)
  exfalso
  obtain ⟨a₀, ha₀A, ha₀W⟩ := Set.not_subset.mp hAW
  set a : ↥(L ⊔ T) := ⟨a₀, Subgroup.mem_sup_right (S_le_T T (hAS ha₀A))⟩ with ha
  have ha1 : F.ρ a ≠ 1 := fun h1 => ha₀W ((F.ρ_eq_one_iff a).1 h1)
  obtain ⟨r, hrP, hr⟩ := surj_of_sup hs hp.P_le hp.sup _ (hs.hB.rho_baum a (hAS ha₀A))
  have hrA : (r : G) ∈ A := hp.mem_of_label hA hp.maxP
    (fun b hb => surj_of_sup hs hp.P_le hp.sup _ (hs.hB.rho_baum b (hAS hb))) a r ha₀A hrP hr
  have hrC : (r : G) ∈ Subgroup.centralizer (W : Set G) := by
    have h1 : (r : G) ∈ Subgroup.centralizer ((P ⊔ A : Subgroup G) : Set G) := by
      refine mem_centralizer_sup ?_ ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro q hq
        have := hp.maxP.2.1.1
        exact setLike_mul_comm hq hrP
      · rw [Subgroup.mem_centralizer_iff]
        intro q hq
        have := hA.2.1.1
        exact setLike_mul_comm hq hrA
    rw [hsup] at h1
    exact Subgroup.centralizer_le hs.hB.le_baum h1
  exact ha1 (hr.symm.trans ((F.ρ_eq_one_iff r).2 hrC))

theorem Partner.label_of_ne (hp : hs.Partner P) {A : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hAQ : A ≠ baum T ⊓ Subgroup.centralizer (W : Set G)) (hAP : A ≠ P) :
    ∃ a₀ : ↥(L ⊔ T), (a₀ : G) ∈ A ∧ (F.ρ a₀ = swap 0 1 ∨ F.ρ a₀ = swap 2 3) ∧
      ∀ a : ↥(L ⊔ T), (a : G) ∈ A → F.ρ a = 1 ∨ F.ρ a = F.ρ a₀ := by
  classical
  have hAS := le_S_of_isMax hA
  have hQmax := hs.isMax_Q hp.elQ
  have hAW : ¬ A ≤ Subgroup.centralizer (W : Set G) := fun hle =>
    hAQ (Subgroup.eq_of_le_of_card_ge (le_inf hAS hle) (hA.2.2 _ hQmax.1 hQmax.2.1))
  obtain ⟨⟨a₀, ha₀A, ha₀⟩, -⟩ := hs.hB.offender_eq hA hAW
  refine ⟨a₀, ha₀A, ha₀, fun a ha => ?_⟩
  by_contra hcon
  push Not at hcon
  have ha₀E : InE4 (F.ρ a₀) := by rcases ha₀ with h | h <;> rw [h] <;> decide
  have ha₀1 : F.ρ a₀ ≠ 1 := by rcases ha₀ with h | h <;> rw [h] <;> decide
  apply hAP
  refine hp.eq_P_of_sup hA (hs.sup_eq_of_surj hAS fun ε hε => ?_)
  rcases e4_cases (F.ρ a₀) (F.ρ a) ε ha₀E (hs.hB.rho_baum a (hAS ha)) hε ha₀1 hcon.1 hcon.2 with
    h | h | h | h
  · exact ⟨1, A.one_mem, by rw [h, map_one]⟩
  · exact ⟨a₀, ha₀A, h.symm⟩
  · exact ⟨a, ha, h.symm⟩
  · exact ⟨a₀ * a, A.mul_mem ha₀A ha, by rw [map_mul, h]⟩

end Setting

end CFSG.Quasithin.H13.A5Push
