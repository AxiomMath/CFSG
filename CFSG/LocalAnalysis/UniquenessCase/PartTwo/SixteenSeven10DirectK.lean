module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectSupport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {T : Type} [CommGroup T] [Finite T]

private theorem s16c1610_dK_dParam_three : dParam 3 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

private theorem s16c1610_dK_card_elemAbelianOfRank {X : Type} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem s16c1610_dK_rank_comm_pow {p n : ℕ} {P : Type} [Group P]
    (h : IsElemAbelianOfRank p n P) :
    (∀ a b : P, a * b = b * a) ∧ ∀ a : P, a ^ p = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp

private theorem s16c1610_dK_eq_one_of_fix_summands {ι : Type} {Y : ι → Subgroup T}
    (hsup : ⨆ i, Y i = ⊤) {x : MulAut T} (h : ∀ i, ∀ v ∈ Y i, x v = v) : x = 1 := by
  have hle : (⨆ i, Y i) ≤ fixV (Subgroup.zpowers x) :=
    iSup_le fun i v hv => mem_fixV_zpowers_iff_apply_eq.2 (h i v hv)
  rw [hsup] at hle
  ext v
  exact mem_fixV_zpowers_iff_apply_eq.1 (hle (Subgroup.mem_top v))

private theorem s16c1610_dK_fix_of_conj_eq {ι : Type} {Y : ι → Subgroup T} {s : ι}
    (hT : ∀ t : T, t ^ 2 = 1) (hcardY : Nat.card ↥(Y s) = 4) {a c : MulAut T}
    (ha3 : a ^ 3 = 1) (hc2 : c ^ 2 = 1) (haY : (Y s).map a.toMonoidHom = Y s)
    (hcY : (Y s).map c.toMonoidHom = Y s) (hca : c * a = a * c)
    (hcs : ∃ y ∈ Y s, c y ≠ y) : a ∈ centSub (Y s) := by
  classical
  obtain ⟨y, hy, hcyne⟩ := hcs
  have haY_mem : ∀ v ∈ Y s, a v ∈ Y s := by
    intro v hv
    have : a v ∈ (Y s).map a.toMonoidHom := Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    rwa [haY] at this
  have hcY_mem : ∀ v ∈ Y s, c v ∈ Y s := by
    intro v hv
    have : c v ∈ (Y s).map c.toMonoidHom := Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    rwa [hcY] at this
  have hca_apply : ∀ v : T, c (a v) = a (c v) := by
    intro v
    have := congrArg (fun f : MulAut T => f v) hca
    simpa [MulAut.mul_apply] using this
  have hcc : c (c y) = y := by
    have := congrArg (fun f : MulAut T => f y) hc2
    simpa [pow_two, MulAut.mul_apply] using this
  have hy1 : y ≠ 1 := by
    intro h
    exact hcyne (by rw [h]; simp)
  have hcy1 : c y ≠ 1 := by
    intro h
    apply hy1
    have := congrArg c h
    rwa [hcc, map_one] at this
  set z : T := y * c y with hzdef
  have hcy_mem : c y ∈ Y s := hcY_mem y hy
  have hz_mem : z ∈ Y s := by rw [hzdef]; exact (Y s).mul_mem hy hcy_mem
  have hcz : c z = z := by
    rw [hzdef, map_mul, hcc, mul_comm]
  have hz1 : z ≠ 1 := by
    intro h
    have h2 : y * y = 1 := by simpa [pow_two] using hT y
    have h1 : z * y = y := by rw [h]; simp
    have h3 : z * y = c y := by
      rw [hzdef]
      calc (y * c y) * y = c y * (y * y) := by ac_rfl
        _ = c y * 1 := by rw [h2]
        _ = c y := by rw [mul_one]
    exact hcyne (h3 ▸ h1)
  have hzy : z ≠ y := by
    intro h
    apply hcy1
    have h1 : y * c y = y * 1 := by rw [← hzdef, h, mul_one]
    exact mul_left_cancel h1
  have hzcy : z ≠ c y := by
    intro h
    apply hy1
    have h1 : y * c y = 1 * c y := by rw [← hzdef, h, one_mul]
    exact mul_right_cancel h1
  have hS_card : ({1, y, c y, z} : Set T).ncard = 4 := by
    have h1 : (1 : T) ∉ ({y, c y, z} : Set T) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hy1.symm, hcy1.symm, hz1.symm⟩
    have h2 : y ∉ ({c y, z} : Set T) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hcyne.symm, hzy.symm⟩
    have h3 : c y ∉ ({z} : Set T) := by
      simpa using hzcy.symm
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
  have hYs_card : (Y s : Set T).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcardY
  have hsub : ({1, y, c y, z} : Set T) ⊆ (Y s : Set T) := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact (Y s).one_mem
    · exact hy
    · exact hcy_mem
    · exact hz_mem
  have hS_eq : ({1, y, c y, z} : Set T) = (Y s : Set T) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hYs_card, hS_card])
  have hfix_eq : ∀ w ∈ Y s, c w = w → w = 1 ∨ w = z := by
    intro w hw hcw
    have hwS : w ∈ ({1, y, c y, z} : Set T) := by rw [hS_eq]; exact hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwS
    rcases hwS with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hcw hcyne
    · exact absurd (hcw.symm.trans hcc) hcyne
    · exact Or.inr rfl
  have haz : a z = z := by
    have haz_mem : a z ∈ Y s := haY_mem z hz_mem
    have haz_fix : c (a z) = a z := by rw [hca_apply, hcz]
    have haz1 : a z ≠ 1 := by
      intro h
      apply hz1
      exact a.injective (by rw [h, map_one])
    rcases hfix_eq (a z) haz_mem haz_fix with h | h
    · exact absurd h haz1
    · exact h
  have hay1 : a y ≠ 1 := by
    intro h
    apply hy1
    exact a.injective (by rw [h, map_one])
  have hayz : a y ≠ z := by
    intro h
    have hfix : c (a y) = a y := by rw [h, hcz]
    have h2 : c (a y) = a (c y) := hca_apply y
    rw [h2] at hfix
    exact hcyne (a.injective hfix)
  have hay : a y = y := by
    have hay_mem : a y ∈ Y s := haY_mem y hy
    have hayS : a y ∈ ({1, y, c y, z} : Set T) := by rw [hS_eq]; exact hay_mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hayS
    rcases hayS with h | h | h | h
    · exact absurd h hay1
    · exact h
    · exfalso
      have h3 : a (a y) = y := by
        rw [h]
        calc a (c y) = c (a y) := (hca_apply y).symm
          _ = c (c y) := by rw [h]
          _ = y := hcc
      have h9 : (a ^ 3) y = a (a (a y)) := by
        rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply]
      have h8 : (a ^ 3) y = y := by
        have := congrArg (fun f : MulAut T => f y) ha3
        simpa using this
      rw [h9] at h8
      have h11 : a (a (a y)) = a y := by rw [h3]
      rw [h11] at h8
      exact hcyne (h ▸ h8)
    · exact absurd h hayz
  refine mem_centSub.mpr ?_
  intro w hw
  have hwS : w ∈ ({1, y, c y, z} : Set T) := by rw [hS_eq]; exact hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwS
  rcases hwS with rfl | rfl | rfl | rfl
  · exact map_one a
  · exact hay
  · rw [← hca_apply y, hay]
  · exact haz

private theorem s16c1610_dK_phi_fix {ι : Type} {A : Subgroup (MulAut T)} {Y : ι → Subgroup T}
    (hAY : ∀ a ∈ A, ∀ s, (Y s).map a.toMonoidHom = Y s) {c : MulAut T} {a : ↥A} {s : ι}
    (hcl : ∀ v ∈ Y s, c v = v) :
    ((a : MulAut T)⁻¹ * (c * (a : MulAut T) * c⁻¹)) ∈ centSub (Y s) := by
  rw [mem_centSub]
  intro v hv
  have hcv : c v = v := hcl v hv
  have hcvi : c⁻¹ v = v := by
    change c.symm v = v
    exact (Equiv.symm_apply_eq c.toEquiv).2 hcv.symm
  have hav : (a : MulAut T) v ∈ Y s := by
    have : (a : MulAut T) v ∈ (Y s).map (a : MulAut T).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    rwa [hAY a a.2 s] at this
  show ((a : MulAut T)⁻¹ * (c * (a : MulAut T) * c⁻¹)) v = v
  simp only [MulAut.mul_apply, hcvi]
  rw [show c ((a : MulAut T) v) = (a : MulAut T) v from hcl _ hav]
  simp

private theorem s16c1610_dK_conj_mem {ι : Type} {A X : Subgroup (MulAut T)}
    {Y : ι → Subgroup T}
    (hAn : ∀ m ∈ X, ∀ a ∈ A, m * a * m⁻¹ ∈ A)
    {s t : ι} {g : MulAut T} (hg : g ∈ X) (hgst : (Y s).map g.toMonoidHom = Y t)
    {a : MulAut T} (ha : a ∈ A) (hfix : a ∈ centSub (Y s)) :
    g * a * g⁻¹ ∈ A ⊓ centSub (Y t) := by
  refine ⟨hAn g hg a ha, ?_⟩
  change g * a * g⁻¹ ∈ centSub (Y t)
  rw [mem_centSub]
  intro v hv
  have hvmap : v ∈ (Y s).map g.toMonoidHom := by rw [hgst]; exact hv
  obtain ⟨v0, hv0, hgv0⟩ := Subgroup.mem_map.mp hvmap
  have hfixv0 : a v0 = v0 := (mem_centSub.mp hfix) v0 hv0
  have hgv : g⁻¹ v = v0 := by rw [← hgv0]; simp
  calc (g * a * g⁻¹) v = g (a (g⁻¹ v)) := by simp [MulAut.mul_apply]
    _ = g (a v0) := by rw [hgv]
    _ = g v0 := by rw [hfixv0]
    _ = v := hgv0

private theorem s16c1610_dK_conj_mem_iff {ι : Type} {A X : Subgroup (MulAut T)}
    {Y : ι → Subgroup T}
    (hAn : ∀ m ∈ X, ∀ a ∈ A, m * a * m⁻¹ ∈ A)
    {s t : ι} {g : MulAut T} (hg : g ∈ X) (hgst : (Y s).map g.toMonoidHom = Y t)
    {a : MulAut T} (ha : a ∈ A) :
    a ∈ centSub (Y s) ↔ g * a * g⁻¹ ∈ centSub (Y t) := by
  constructor
  · intro h
    exact (s16c1610_dK_conj_mem hAn hg hgst ha h).2
  · intro h
    have hgt : (Y t).map (g⁻¹).toMonoidHom = Y s := by
      have hcomp : (g⁻¹).toMonoidHom.comp g.toMonoidHom = MonoidHom.id T := by
        ext x
        simp [MulAut.mul_apply]
      rw [← hgst, Subgroup.map_map, hcomp, Subgroup.map_id]
    have hA' : g * a * g⁻¹ ∈ A := hAn g hg a ha
    have h2 := (s16c1610_dK_conj_mem hAn (X.inv_mem hg) hgt hA' h).2
    have heq : g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ = a := by group
    rwa [heq] at h2

theorem s16c1610_false_of_involution_on_two (hT : ∀ t : T, t ^ 2 = 1) {ι : Type} [Fintype ι]
    {Y : ι → Subgroup T} {X A : Subgroup (MulAut T)} (hY : SymSumFamily X Y 3 2)
    (hA : IsElemAbelianOfRank 3 3 ↥A) (hAX : A ≤ X)
    (hAn : ∀ m ∈ X, ∀ a ∈ A, m * a * m⁻¹ ∈ A) (hAY : ∀ a ∈ A, ∀ s, (Y s).map a.toMonoidHom = Y s)
    {c : MulAut T} (hcX : c ∈ X) (hc2 : c ^ 2 = 1) (hcY : ∀ s, (Y s).map c.toMonoidHom = Y s)
    {i j l m : ι} (hij : i ≠ j) (hil : i ≠ l) (him : i ≠ m) (hjl : j ≠ l) (hjm : j ≠ m)
    (hlm : l ≠ m) (hci : ∃ y ∈ Y i, c y ≠ y) (hcj : ∃ y ∈ Y j, c y ≠ y)
    (hcl : ∀ y ∈ Y l, c y = y) (hcm : ∀ y ∈ Y m, c y = y) : False := by
  classical
  have hd3 : dParam 3 = 2 := s16c1610_dK_dParam_three
  have hAc := s16c1610_dK_rank_comm_pow hA
  have hAcomm : ∀ a b : ↥A, a * b = b * a := hAc.1
  have hApow : ∀ a : ↥A, a ^ 3 = 1 := hAc.2
  have hAel : IsElemAbelian 3 A :=
    ⟨isMulCommutative_iff.mpr hAcomm, fun x hx => by
      have := hApow ⟨x, hx⟩
      simpa using this⟩
  have hAcard : Nat.card ↥A = 27 := by
    have h := s16c1610_dK_card_elemAbelianOfRank hA
    norm_num at h
    exact h
  have hcardY : ∀ s : ι, Nat.card ↥(Y s) = 4 := by
    intro s
    rw [card_eq_two_pow hT (Y s), hY.rank s]
    norm_num
  have hAs_ne : ∀ s : ι, A ⊓ centSub (Y s) ≠ A := by
    intro s heq
    have hle : A ≤ centSub (Y s) := by
      intro a ha
      have hmem : a ∈ A ⊓ centSub (Y s) := by rw [heq]; exact ha
      exact (Subgroup.mem_inf.mp hmem).2
    have hbot : A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro a ha
      apply s16c1610_dK_eq_one_of_fix_summands hY.sup
      intro t v hv
      obtain ⟨g, hgX, hg⟩ := hY.surj (Equiv.swap s t)
      have hgs : (Y s).map g.toMonoidHom = Y t := by rw [hg s, Equiv.swap_apply_left]
      have ha' : (g⁻¹ : MulAut T) * a * (g⁻¹)⁻¹ ∈ A := hAn (g⁻¹) (X.inv_mem hgX) a ha
      have hfix' : ((g⁻¹ : MulAut T) * a * (g⁻¹)⁻¹) ∈ centSub (Y s) := hle ha'
      have hvmap : v ∈ (Y s).map g.toMonoidHom := by rw [hgs]; exact hv
      obtain ⟨v0, hv0, hgv0⟩ := Subgroup.mem_map.mp hvmap
      have hfixv0 : ((g⁻¹ : MulAut T) * a * (g⁻¹)⁻¹) v0 = v0 :=
        (mem_centSub.mp hfix') v0 hv0
      have hgv : g⁻¹ v = v0 := by rw [← hgv0]; simp
      have hg_eq : g * ((g⁻¹ : MulAut T) * a * (g⁻¹)⁻¹) * g⁻¹ = a := by group
      calc a v = (g * ((g⁻¹ : MulAut T) * a * (g⁻¹)⁻¹) * g⁻¹) v := by rw [hg_eq]
        _ = g (((g⁻¹ : MulAut T) * a * (g⁻¹)⁻¹) (g⁻¹ v)) := by simp [MulAut.mul_apply]
        _ = g (((g⁻¹ : MulAut T) * a * (g⁻¹)⁻¹) v0) := by rw [hgv]
        _ = g v0 := by rw [hfixv0]
        _ = v := hgv0
    have h1 : Nat.card ↥A = 1 := by rw [hbot]; simp
    omega
  have hAs_card : ∀ s : ι, Nat.card ↥(A ⊓ centSub (Y s)) = 9 := by
    intro s
    have hidx := s16n9b_case4_aut_index_le (Or.inl rfl) hT
      (by rw [hY.rank s, hd3]) hAel (fun f hf => hAY f hf s)
    have hle9 : 9 ≤ Nat.card ↥(A ⊓ centSub (Y s)) := by
      have h := hidx
      rw [hAcard] at h
      omega
    have hdvd : Nat.card ↥(A ⊓ centSub (Y s)) ∣ 3 ^ 3 := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ centSub (Y s) ≤ A)
      rw [hAcard] at h
      simpa using h
    have hnlt : Nat.card ↥(A ⊓ centSub (Y s)) < 27 := by
      by_contra hge
      push Not at hge
      exact hAs_ne s (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hAcard]; exact hge))
    obtain ⟨k, hk3, hk⟩ :=
      (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).1 hdvd
    have hle_k : 9 ≤ 3 ^ k := by rw [← hk]; exact hle9
    have hlt_k : 3 ^ k < 27 := by rw [← hk]; exact hnlt
    have hk0 : k ≠ 0 := by rintro rfl; norm_num at hle_k
    have hk1 : k ≠ 1 := by rintro rfl; norm_num at hle_k
    have hk3' : k ≠ 3 := by rintro rfl; norm_num at hlt_k
    have hk_eq : k = 2 := by
      clear hle_k hlt_k
      omega
    rw [hk, hk_eq]
    norm_num
  have hAs_inf : ∀ s s' : ι, s ≠ s' →
      Nat.card ↥((A ⊓ centSub (Y s)) ⊓ (A ⊓ centSub (Y s'))) ≤ 3 := by
    intro s s' hss'
    by_contra h
    push Not at h
    have hdvd : Nat.card ↥((A ⊓ centSub (Y s)) ⊓ (A ⊓ centSub (Y s'))) ∣ 9 := by
      have hh := Subgroup.card_dvd_of_le
        (inf_le_left : (A ⊓ centSub (Y s)) ⊓ (A ⊓ centSub (Y s')) ≤ A ⊓ centSub (Y s))
      rwa [hAs_card s] at hh
    have hdvd' : Nat.card ↥((A ⊓ centSub (Y s)) ⊓ (A ⊓ centSub (Y s'))) ∣ 3 ^ 2 := by
      simpa using hdvd
    obtain ⟨k, hk2, hk⟩ :=
      (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).1 hdvd'
    have hkgt : 3 < 3 ^ k := by rw [← hk]; exact h
    have hk0 : k ≠ 0 := by rintro rfl; norm_num at hkgt
    have hk1 : k ≠ 1 := by rintro rfl; norm_num at hkgt
    have hk_eq : k = 2 := by
      clear hkgt
      omega
    have hge : 9 ≤ Nat.card ↥((A ⊓ centSub (Y s)) ⊓ (A ⊓ centSub (Y s'))) := by
      rw [hk, hk_eq]
      norm_num
    have heq : (A ⊓ centSub (Y s)) ⊓ (A ⊓ centSub (Y s')) = A ⊓ centSub (Y s) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hAs_card s]; exact hge)
    have hEq : A ⊓ centSub (Y s) = A ⊓ centSub (Y s') := by
      apply Subgroup.eq_of_le_of_card_ge
      · intro a ha
        have : a ∈ (A ⊓ centSub (Y s)) ⊓ (A ⊓ centSub (Y s')) := by rw [heq]; exact ha
        exact (Subgroup.mem_inf.mp this).2
      · rw [hAs_card s', hAs_card s]
    have hEq_iff : ∀ a ∈ A, (a ∈ centSub (Y s) ↔ a ∈ centSub (Y s')) := by
      intro a ha
      have h1 : a ∈ A ⊓ centSub (Y s) ↔ a ∈ A ⊓ centSub (Y s') := by rw [hEq]
      constructor
      · intro hc
        have hmem : a ∈ A ⊓ centSub (Y s') := h1.mp ⟨ha, hc⟩
        exact (Subgroup.mem_inf.mp hmem).2
      · intro hc
        have hmem : a ∈ A ⊓ centSub (Y s) := h1.mpr ⟨ha, hc⟩
        exact (Subgroup.mem_inf.mp hmem).2
    have hall : ∀ t, A ⊓ centSub (Y t) = A ⊓ centSub (Y s) := by
      intro t
      by_cases hts : t = s
      · rw [hts]
      · by_cases hts' : t = s'
        · rw [hts', ← hEq]
        · obtain ⟨g, hgX, hg⟩ := hY.surj (Equiv.swap s t)
          have hgs : (Y s).map g.toMonoidHom = Y t := by rw [hg s, Equiv.swap_apply_left]
          have hgs' : (Y s').map g.toMonoidHom = Y s' := by
            rw [hg s', Equiv.swap_apply_of_ne_of_ne hss'.symm (Ne.symm hts')]
          have hgt_le : A ⊓ centSub (Y t) ≤ A ⊓ centSub (Y s') := by
            intro a' ha'
            have hA' : a' ∈ A := ha'.1
            have hc' : a' ∈ centSub (Y t) := ha'.2
            have ha0 : (g⁻¹ : MulAut T) * a' * (g⁻¹)⁻¹ ∈ A :=
              hAn (g⁻¹) (X.inv_mem hgX) a' hA'
            have hga0 : g * ((g⁻¹ : MulAut T) * a' * (g⁻¹)⁻¹) * g⁻¹ = a' := by group
            have h1 : ((g⁻¹ : MulAut T) * a' * (g⁻¹)⁻¹) ∈ centSub (Y s) :=
              (s16c1610_dK_conj_mem_iff hAn hgX hgs ha0).mpr (by rw [hga0]; exact hc')
            have h2 : ((g⁻¹ : MulAut T) * a' * (g⁻¹)⁻¹) ∈ centSub (Y s') :=
              (hEq_iff _ ha0).mp h1
            have h3 : a' ∈ centSub (Y s') := by
              have h3' := (s16c1610_dK_conj_mem_iff hAn hgX hgs' ha0).mp h2
              rwa [hga0] at h3'
            exact ⟨hA', h3⟩
          have hs'_le : A ⊓ centSub (Y s') ≤ A ⊓ centSub (Y t) := by
            intro a' ha'
            have hA' : a' ∈ A := ha'.1
            have hc' : a' ∈ centSub (Y s') := ha'.2
            have ha0 : (g⁻¹ : MulAut T) * a' * (g⁻¹)⁻¹ ∈ A :=
              hAn (g⁻¹) (X.inv_mem hgX) a' hA'
            have hga0 : g * ((g⁻¹ : MulAut T) * a' * (g⁻¹)⁻¹) * g⁻¹ = a' := by group
            have h1 : ((g⁻¹ : MulAut T) * a' * (g⁻¹)⁻¹) ∈ centSub (Y s') :=
              (s16c1610_dK_conj_mem_iff hAn hgX hgs' ha0).mpr (by rw [hga0]; exact hc')
            have h2 : ((g⁻¹ : MulAut T) * a' * (g⁻¹)⁻¹) ∈ centSub (Y s) :=
              (hEq_iff _ ha0).mpr h1
            have h3 : a' ∈ centSub (Y t) := by
              have h3' := (s16c1610_dK_conj_mem_iff hAn hgX hgs ha0).mp h2
              rwa [hga0] at h3'
            exact ⟨hA', h3⟩
          have ht_eq : A ⊓ centSub (Y t) = A ⊓ centSub (Y s') := le_antisymm hgt_le hs'_le
          rw [ht_eq]
          exact hEq.symm
    have hbot : A ⊓ centSub (Y s) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro a ha
      apply s16c1610_dK_eq_one_of_fix_summands hY.sup
      intro t v hv
      have hat : a ∈ A ⊓ centSub (Y t) := by rw [hall t]; exact ha
      exact (mem_centSub.mp (Subgroup.mem_inf.mp hat).2) v hv
    have h1 : Nat.card ↥(A ⊓ centSub (Y s)) = 1 := by rw [hbot]; simp
    exact absurd h1 (by rw [hAs_card s]; norm_num)
  letI : CommGroup ↥A := { (inferInstance : Group ↥A) with mul_comm := hAcomm }
  let conj : ↥A →* ↥A :=
    { toFun := fun a => ⟨c * (a : MulAut T) * c⁻¹, hAn c hcX a.1 a.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        show c * ((a * b : ↥A) : MulAut T) * c⁻¹ =
          (c * (a : MulAut T) * c⁻¹) * (c * (b : MulAut T) * c⁻¹)
        rw [show ((a * b : ↥A) : MulAut T) = (a : MulAut T) * (b : MulAut T) from rfl]
        group }
  let φ : ↥A →* ↥A := invMonoidHom * conj
  have hφ_apply : ∀ a : ↥A, φ a = (a : ↥A)⁻¹ * conj a := fun a => rfl
  have hφ_val : ∀ a : ↥A, (φ a : MulAut T) =
      (a : MulAut T)⁻¹ * (c * (a : MulAut T) * c⁻¹) := by
    intro a
    rw [hφ_apply]
    rfl
  have hker_fix : ∀ (s : ι), (∃ y ∈ Y s, c y ≠ y) → ∀ b : ↥A, b ∈ φ.ker →
      (b : MulAut T) ∈ A ⊓ centSub (Y s) := by
    intro s hcs b hb
    have hb1 : φ b = 1 := MonoidHom.mem_ker.mp hb
    have hb2 : conj b = b := by
      have h1 : (b : ↥A)⁻¹ * conj b = 1 := by rw [← hφ_apply]; exact hb1
      have := congrArg (fun x : ↥A => (b : ↥A) * x) h1
      rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at this
      exact this
    have hconj : c * (b : MulAut T) * c⁻¹ = (b : MulAut T) := congrArg Subtype.val hb2
    have hca : c * (b : MulAut T) = (b : MulAut T) * c := by
      calc c * (b : MulAut T) = (c * (b : MulAut T) * c⁻¹) * c := by group
        _ = (b : MulAut T) * c := by rw [hconj]
    have hb3 : (b : MulAut T) ^ 3 = 1 := by
      simpa using congrArg Subtype.val (hApow b)
    refine ⟨b.2, ?_⟩
    exact s16c1610_dK_fix_of_conj_eq (Y := Y) (s := s) (a := (b : MulAut T)) hT (hcardY s)
      hb3 hc2 (hAY b b.2 s) (hcY s) hca hcs
  have hKle : φ.ker.map A.subtype ≤ (A ⊓ centSub (Y i)) ⊓ (A ⊓ centSub (Y j)) := by
    rintro x ⟨b, hb, rfl⟩
    exact ⟨hker_fix i hci b hb, hker_fix j hcj b hb⟩
  have himage_fix : ∀ (s : ι), (∀ y ∈ Y s, c y = y) → ∀ a : ↥A,
      (φ a : MulAut T) ∈ A ⊓ centSub (Y s) := by
    intro s hcl' a
    refine ⟨(φ a).2, ?_⟩
    rw [hφ_val a]
    exact s16c1610_dK_phi_fix (A := A) (Y := Y) hAY hcl'
  have hRangeLe : φ.range.map A.subtype ≤ (A ⊓ centSub (Y l)) ⊓ (A ⊓ centSub (Y m)) := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    exact ⟨himage_fix l hcl a, himage_fix m hcm a⟩
  have hKcard : Nat.card φ.ker ≤ 3 := by
    have h1 : Nat.card (φ.ker.map A.subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective A.subtype_injective
    have h2 : Nat.card (φ.ker.map A.subtype) ≤
        Nat.card ↥((A ⊓ centSub (Y i)) ⊓ (A ⊓ centSub (Y j))) :=
      Subgroup.card_le_of_le hKle
    have h3 := hAs_inf i j hij
    omega
  have hRcard : Nat.card φ.range ≤ 3 := by
    have h1 : Nat.card (φ.range.map A.subtype) = Nat.card φ.range :=
      Subgroup.card_map_of_injective A.subtype_injective
    have h2 : Nat.card (φ.range.map A.subtype) ≤
        Nat.card ↥((A ⊓ centSub (Y l)) ⊓ (A ⊓ centSub (Y m))) :=
      Subgroup.card_le_of_le hRangeLe
    have h3 := hAs_inf l m hlm
    omega
  have hker_card := Subgroup.card_ker_mul_card_range φ
  have h9 : 9 ≤ Nat.card φ.ker := by
    have h1 : Nat.card φ.ker * Nat.card φ.range = 27 := by
      rw [hker_card, hAcard]
    have h2 : Nat.card φ.ker * Nat.card φ.range ≤ Nat.card φ.ker * 3 :=
      Nat.mul_le_mul_left _ hRcard
    rw [h1] at h2
    omega
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
