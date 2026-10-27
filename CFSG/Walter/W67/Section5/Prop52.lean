module

public import CFSG.Walter.W67.Section5.Sylow52
public import CFSG.Walter.W67.Section5.Lemma54
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.theorem_14_4_2

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Borel5

variable {F : Type} [Field F]

theorem unip_comm {a b : PSL(2, F)} (ha : a ∈ unip F) (hb : b ∈ unip F) : a * b = b * a := by
  obtain ⟨y, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff a).mp ha
  obtain ⟨z, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff b).mp hb
  rw [← map_mul, ← map_mul, sl2UpperUnipotent_mul, sl2UpperUnipotent_mul, add_comm]

theorem sl2UpperUnipotent_pow (y : F) (n : ℕ) :
    sl2UpperUnipotent y ^ n = sl2UpperUnipotent ((n : F) * y) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, sl2UpperUnipotent_zero]
  | succ n ih => rw [pow_succ, ih, sl2UpperUnipotent_mul, Nat.cast_succ, add_mul, one_mul]

theorem unip_pow_char {p : ℕ} [CharP F p] {a : PSL(2, F)} (ha : a ∈ unip F) : a ^ p = 1 := by
  obtain ⟨y, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff a).mp ha
  rw [← map_pow, sl2UpperUnipotent_pow, CharP.cast_eq_zero, zero_mul, sl2UpperUnipotent_zero,
    map_one]

end Borel5

namespace Sec52

theorem mem_normalizer_sup {A C : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hC : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := by
  apply Sec53.mem_normalizer_of_conj_le
  have hle : A ⊔ C ≤ (A ⊔ C).comap (MulAut.conj g).toMonoidHom := sup_le
    (fun a ha => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA a).mp ha))
    (fun c hc => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hC c).mp hc))
  exact fun y hy => hle hy

omit [Finite G] in
theorem centralizer_zpowers_eq (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  ext y
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h x (Subgroup.mem_zpowers x)).symm
  · intro h z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (h.symm : Commute x y) k).eq

end Sec52

namespace Frame5

variable {s : Std G} (f5 : Frame5 s)

theorem P₁_comm : ∀ a ∈ f5.P₁, ∀ b ∈ f5.P₁, a * b = b * a := by
  obtain ⟨g, hP₁, -⟩ := f5.exists_std
  intro a ha b hb
  rw [hP₁] at ha hb
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
  obtain ⟨a'', ha'', rfl⟩ := Subgroup.mem_map.mp ha'
  obtain ⟨b'', hb'', rfl⟩ := Subgroup.mem_map.mp hb'
  simp only [← map_mul, Borel5.unip_comm ha'' hb'']

theorem P₁_pow : ∀ a ∈ f5.P₁, a ^ s.p = 1 := by
  obtain ⟨g, hP₁, -⟩ := f5.exists_std
  intro a ha
  rw [hP₁] at ha
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨a'', ha'', rfl⟩ := Subgroup.mem_map.mp ha'
  rw [← map_pow, ← map_pow, Borel5.unip_pow_char ha'', map_one, map_one]

theorem K_inf_centralizer_le
    {k : G} (hkK : k ∈ s.K)
    (hkC : k ∈ Subgroup.centralizer (f5.P₁ : Set G)) : k ∈ f5.P₁ := by
  have hP₁1 : f5.P₁ ≠ ⊥ := by
    intro h
    have := f5.card_P₁
    rw [h, Subgroup.card_bot] at this
    have := s.three_lt_q
    omega
  have hBN : f5.B ≤ Subgroup.normalizer (f5.P₁ : Set G) :=
    fun b hb => f5.B_le_normalizer (Subgroup.mem_sup_left hb)
  have hEN : s.fr.E ≤ Subgroup.normalizer ((f5.P₁ ⊔ f5.B : Subgroup G) : Set G) :=
    fun e he => Sec52.mem_normalizer_sup (f5.B_le_normalizer (Subgroup.mem_sup_right he))
      (f5.E_le_normalizer_B he)
  have hk : k ∈ Subgroup.normalizer (f5.P₁ : Set G) ⊓ (s.K ⊔ s.fr.E) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.centralizer_le_normalizer _ hkC, Subgroup.mem_sup_left hkK⟩
  rw [f5.normalizer_eq] at hk
  obtain ⟨y, hy, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEN).mp hk
  obtain ⟨u, hu, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hBN).mp hy
  have hub : u * b ∈ s.K := s.K.mul_mem (f5.P₁_le hu) (f5.B_le hb)
  have he1 : e = 1 := by
    have heK : e ∈ s.K := by
      have := s.K.mul_mem (s.K.inv_mem hub) hkK
      rwa [inv_mul_cancel_left] at this
    have : e ∈ s.K ⊓ s.fr.E := Subgroup.mem_inf.mpr ⟨heK, he⟩
    rwa [s.fr.K_inf_E, Subgroup.mem_bot] at this
  subst he1
  rw [mul_one] at hkC ⊢
  have hbC : b ∈ Subgroup.centralizer (f5.P₁ : Set G) := by
    have huC : u⁻¹ ∈ Subgroup.centralizer (f5.P₁ : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz => f5.P₁_comm z hz _ (f5.P₁.inv_mem hu)
    have := Subgroup.mul_mem _ huC hkC
    rwa [inv_mul_cancel_left] at this
  have hb1 : b = 1 := by
    by_contra hb1
    apply hP₁1
    have h0 := f5.fixedPointFree b hb hb1
    rw [eq_bot_iff, ← h0]
    intro z hz
    exact Subgroup.mem_inf.mpr ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hbC z hz)⟩
  rw [hb1, mul_one]
  exact hu

end Frame5

open Frame5 Borel5 Sec52 in
theorem prop_5_2_of
    (h26i : S_lemma_2_6_i) (hJR : S_IsJRSubgroup_nonempty_jrGroup) :
    ∀ (G : Type) [Group G] [Finite G] (s : Std G), s.p = 5 → JFacts → RFacts →
      ¬ 5 ∣ Nat.card s.fr.E := by
  intro G _ _ s hp hJ hR h5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨⟨x, hxE⟩, hox⟩ := exists_prime_orderOf_dvd_card' (G := s.fr.E) 5 h5
  rw [Subgroup.orderOf_mk] at hox
  set X := Subgroup.zpowers x with hXdef
  have hXE : X ≤ s.fr.E := Subgroup.zpowers_le.mpr hxE
  have hXcard : Nat.card X = 5 := by rw [Nat.card_zpowers, hox]
  have hX1 : X ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hXcard
    norm_num at hXcard
  have hCX' : Subgroup.centralizer (X : Set G) = Subgroup.centralizer ({x} : Set G) :=
    centralizer_zpowers_eq x
  have heX : ∀ Y : Subgroup G, s.eX Y = Nat.card Y := fun Y => by
    rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one]
  obtain ⟨hediv, ⟨eKX⟩, -⟩ := h26i G s.toHyp s.fr hXE hX1
  have h5f : 5 ∣ s.f := by
    have := hediv
    rwa [heX, hXcard] at this
  have hLS := s.L_spec X hXE hX1
  obtain ⟨K', hK'jr, -⟩ := hLS.jr
  have hfe : s.f / s.eX X = s.f / 5 := by rw [heX, hXcard]
  have hfpos : 0 < s.f / s.eX X := by
    rw [hfe]
    exact Nat.div_pos (Nat.le_of_dvd s.f_pos h5f) (by norm_num)
  obtain ⟨hL', hL'p, hL'f, -, -⟩ := hJR G s.p_ne_two hfpos hK'jr
  have hq' : hL'.q = 5 ^ (s.f / 5) := by rw [JRGroup.q, hL'p, hL'f, hfe, hp]
  have hf5 : s.f / 5 = 1 := by
    by_contra hne
    have hq'5 : hL'.q ≠ 5 := by
      rw [hq']
      intro h
      exact hne (Nat.pow_right_injective (by norm_num : 2 ≤ 5) (h.trans (pow_one 5).symm))
    obtain ⟨n, -, hn⟩ := (hR _ hL' hq'5).1.1
    rw [hq'] at hn
    have h5dvd : 5 ∣ 3 ^ n := by
      rw [← hn]
      exact dvd_pow_self 5 (by rw [hfe] at hfpos; omega)
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5dvd
    norm_num at this
  have hf : s.f = 5 := by
    have := Nat.div_mul_cancel h5f
    omega
  have hq'eq : hL'.q = 5 := by rw [hq', hf5, pow_one]
  obtain ⟨⟨-, hLcard, -⟩, -⟩ := hJ _ hL' hq'eq
  have hEcard : Nat.card s.fr.E = 5 := by
    obtain ⟨hEdiv, -, -⟩ := h26i G s.toHyp s.fr le_rfl s.E_ne_bot
    rw [heX, hf] at hEdiv
    rcases (Nat.dvd_prime (by norm_num)).mp hEdiv with h1 | h1
    · rw [h1] at h5
      norm_num at h5
    · exact h1
  obtain ⟨f5⟩ := Frame5.nonempty s
  have hq : s.q = 5 ^ 5 := by rw [Hyp.q, hp, hf]
  have hP₁card : Nat.card f5.P₁ = 5 ^ 5 := by rw [f5.card_P₁, hq]
  have hxN : x ∈ Subgroup.normalizer (f5.P₁ : Set G) :=
    f5.B_le_normalizer (Subgroup.mem_sup_right hxE)
  have hP₁exp : ∀ a ∈ f5.P₁, a ^ 5 = 1 := fun a ha => by
    rw [← hp]
    exact f5.P₁_pow a ha
  have hP₁p : IsPGroup 5 f5.P₁ := fun g => ⟨1, Subtype.ext (by simpa using hP₁exp _ g.2)⟩
  have hKXcard : Nat.card (s.KX X) = 60 := by
    have hFcard : Nat.card (GaloisField s.p (s.f / s.eX X)) = s.p ^ (s.f / s.eX X) :=
      GaloisField.card s.p _ hfpos.ne'
    rw [Nat.card_congr eKX.toEquiv, psl2_card_formula _ ⟨s.p, s.f / s.eX X, Fact.out, s.odd_p,
      hfpos, hFcard⟩, hFcard, hfe, hf5, hp]
    norm_num
  have hCP₁ : Nat.card (f5.P₁ ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≤ 5 := by
    have hle : f5.P₁ ⊓ Subgroup.centralizer ({x} : Set G) ≤ s.KX X := by
      intro y hy
      obtain ⟨hyP, hyC⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_inf.mpr ⟨f5.P₁_le hyP, ?_⟩
      rw [hCX']
      exact hyC
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hKXcard] at hdvd
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hP₁p.to_le inf_le_left)
    rw [hk] at hdvd ⊢
    by_contra hlt
    have hk2 : 2 ≤ k :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 5)).mp (by rw [pow_one]; omega)
    have := (Nat.pow_dvd_pow 5 hk2).trans hdvd
    norm_num at this
  have hCXeq := hLS.centralizer_eq (by rw [s.F_eq_bot]; exact bot_le)
  have hDN : Subgroup.centralizer (X : Set G) ⊓ s.fr.E ≤
      Subgroup.normalizer ((s.L X : Subgroup G) : Set G) := by
    intro d hd
    apply Sec53.mem_normalizer_of_conj_le
    intro y hy
    have hdN : d ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hd).1
    have hyN : y ∈ Subgroup.normalizer (X : Set G) := hLS.normal.1 hy
    exact Subgroup.mem_subgroupOf.mp (hLS.normal.2.conj_mem ⟨y, hyN⟩
      (Subgroup.mem_subgroupOf.mpr hy) ⟨d, hdN⟩)
  have hCdvd : Nat.card (Subgroup.centralizer (X : Set G)) ∣
      2 ^ 3 * 3 * 5 * 7 * 11 * 19 * 5 := by
    have h1 := card_sup_mul_card_inf hDN
    rw [hCXeq, sup_comm]
    have h3 : Nat.card (Subgroup.centralizer (X : Set G) ⊓ s.fr.E : Subgroup G) ∣ 5 :=
      hEcard ▸ Subgroup.card_dvd_of_le inf_le_right
    rw [← hLcard]
    exact (Dvd.intro _ h1).trans (Nat.mul_dvd_mul_left _ h3)
  have hCx : ∀ R : Subgroup G, IsPGroup 5 R → x ∈ R →
      Nat.card (R ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≤ 5 ^ 2 := by
    intro R hR5 _
    rw [← hCX']
    have hdvd := (Subgroup.card_dvd_of_le
      (inf_le_right : R ⊓ Subgroup.centralizer (X : Set G) ≤ _)).trans hCdvd
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hR5.to_le inf_le_left)
    rw [hk] at hdvd ⊢
    by_contra hlt
    have hk3 : 3 ≤ k := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 5)).mp (by omega)
    have := (Nat.pow_dvd_pow 5 hk3).trans hdvd
    norm_num at this
  have h52 : Hyp52 5 f5.P₁ x :=
    { comm := f5.P₁_comm
      exp := hP₁exp
      normalizes := hxN
      orderOf_x := hox
      card_fix := hCP₁
      card_le := le_of_eq hP₁card.symm
      card_big := by rw [hP₁card]; norm_num
      centralizer := hCx }
  set H := Subgroup.normalizer (f5.P₁ : Set G) with hHdef
  let P : Sylow 5 G := Sylow.ofCard (f5.P₁ ⊔ Subgroup.zpowers x) h52.card_Q_eq
  have hengel : ∀ u z : G, u ∈ f5.P₁ → z ∈ f5.P₁ →
      BenderSuzuki.External.engelSymbol (5 - 1) u z = 1 :=
    fun u z hu hz => iterated_eq_one (f5.P₁_comm u hu z hz) 2
  have hHW := BenderSuzuki.External.hallWielandt_residual_intersection 5 P f5.P₁ H rfl
    h52.weaklyClosedIn (Or.inr (Or.inl hengel))
  have hres : (BenderSuzuki.External.hallPResidual 5 H).map H.subtype = H := by
    rw [hHW.1, hallPResidual_eq_top s.perfect, inf_top_eq]
  set M := Subgroup.centralizer (f5.P₁ : Set G) ⊔ f5.B with hMdef
  have hP₁C : f5.P₁ ≤ Subgroup.centralizer (f5.P₁ : Set G) :=
    fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => f5.P₁_comm b hb a ha
  have hBN : f5.B ≤ H := fun b hb => f5.B_le_normalizer (Subgroup.mem_sup_left hb)
  have hEN : s.fr.E ≤ H := fun e he => f5.B_le_normalizer (Subgroup.mem_sup_right he)
  have hEM : s.fr.E ≤ Subgroup.normalizer (M : Set G) := fun e he =>
    mem_normalizer_sup (Sec54.mem_normalizer_centralizer (hEN he)) (f5.E_le_normalizer_B he)
  have hP₁1 : f5.P₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hP₁card
    norm_num at hP₁card
  have hCB : Subgroup.centralizer (f5.P₁ : Set G) ⊓ f5.B = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨hbC, hbB⟩ := Subgroup.mem_inf.mp hb
    rw [Subgroup.mem_bot]
    by_contra hb1
    apply hP₁1
    rw [eq_bot_iff, ← f5.fixedPointFree b hbB hb1]
    intro z hz
    exact Subgroup.mem_inf.mpr ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hbC z hz)⟩
  have hMcard : Nat.card M =
      Nat.card (Subgroup.centralizer (f5.P₁ : Set G)) * Nat.card f5.B := by
    have h1 := card_sup_mul_card_inf (A := Subgroup.centralizer (f5.P₁ : Set G)) (C := f5.B)
      (fun b hb => Sec54.mem_normalizer_centralizer (hBN hb))
    rw [hCB, Subgroup.card_bot, mul_one, sup_comm] at h1
    exact h1
  have hBcard : Nat.card f5.B = 1562 := by
    have := f5.card_B
    rw [hq] at this
    omega
  have hxM : x ∉ M := by
    intro hxM
    have hQM : f5.P₁ ⊔ Subgroup.zpowers x ≤ M :=
      sup_le (hP₁C.trans le_sup_left) (Subgroup.zpowers_le.mpr hxM)
    have hdvd := Subgroup.card_dvd_of_le hQM
    rw [h52.card_Q, hP₁card, hMcard, hBcard, show 5 * 5 ^ 5 = 5 ^ 6 by norm_num] at hdvd
    have hdvd' := (show Nat.Coprime (5 ^ 6) 1562 by norm_num).dvd_of_dvd_mul_right hdvd
    obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime 5 hdvd'
    have hS' := h52.card_le_of_le_centralizer
      (S := S.map (Subgroup.centralizer (f5.P₁ : Set G)).subtype)
      ((IsPGroup.of_card hS).map _) (Subgroup.map_subtype_le _)
    rw [Subgroup.card_map_of_injective (Subgroup.centralizer _).subtype_injective, hS,
      hP₁card] at hS'
    norm_num at hS'
  have hME : M ⊓ s.fr.E = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    obtain ⟨heM, heE⟩ := Subgroup.mem_inf.mp he
    rw [Subgroup.mem_bot]
    by_contra he1
    apply hxM
    have hoe : orderOf e = 5 := by
      have hdvd : orderOf e ∣ 5 := hEcard ▸ Subgroup.orderOf_dvd_natCard _ heE
      rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) he1
      · exact h1
    have hze : Subgroup.zpowers e = s.fr.E :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr heE)
        (by rw [hEcard, Nat.card_zpowers, hoe])
    have hx' : x ∈ Subgroup.zpowers e := by rw [hze]; exact hxE
    exact Subgroup.zpowers_le.mpr heM hx'
  have hJC : s.J ∈ Subgroup.centralizer (f5.P₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact s.commute_J (s.K_le_H (f5.P₁_le hy))
  have hB1 : ∀ W : Subgroup G, W ≤ Subgroup.centralizer (f5.P₁ : Set G) → s.J ∈ W →
      IsPGroup 2 W → W ≤ Subgroup.zpowers s.J := by
    intro W hWC hJW hW w hw
    have hWab := s.toHyp.isMulCommutative_of_isPGroup hW
    have hwJc : Commute s.J w :=
      congrArg Subtype.val (hWab.is_comm.comm ⟨s.J, hJW⟩ ⟨w, hw⟩)
    have hww : w * w = 1 := s.fr.mul_self_of_isPGroup (hW.to_le (Subgroup.zpowers_le.mpr hw))
    have hwC : w ∈ Subgroup.centralizer (f5.P₁ : Set G) := hWC hw
    have hwH : w ∈ s.H := Subgroup.mem_centralizer_singleton_iff.mpr hwJc.eq.symm
    obtain ⟨j, hj, m, hm, rfl⟩ := s.fr.exists_decomp_H_JM hwH
    have hjc : ∀ y ∈ s.K ⊔ s.fr.E, j * y = y * j := fun y hy => s.fr.commute_of_mem_KE hj hy
    have hjj : j * j = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers s.orderOf_J hj with rfl | rfl
      · exact mul_one 1
      · exact s.J_mul_J
    have hmm : m * m = 1 := by
      calc m * m = (j * j)⁻¹ * (j * (j * m) * m) := by group
        _ = (j * j)⁻¹ * (j * (m * j) * m) := by rw [hjc m hm]
        _ = (j * j)⁻¹ * ((j * m) * (j * m)) := by group
        _ = 1 := by rw [hww, hjj]; group
    have hmK := s.fr.mem_K_of_mem_KE_of_mul_self hm hmm
    have hmC : m ∈ Subgroup.centralizer (f5.P₁ : Set G) := by
      have h1 : m = j⁻¹ * (j * m) := by group
      rw [h1]
      exact mul_mem (inv_mem (Subgroup.zpowers_le.mpr hJC hj)) hwC
    have hmP := f5.K_inf_centralizer_le hmK hmC
    have hm1 : m = 1 := by
      have h2 : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hmm])
      have h55 : orderOf m ∣ 5 ^ 5 := hP₁card ▸ Subgroup.orderOf_dvd_natCard _ hmP
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left h2 (by norm_num)) h55)
    rw [hm1, mul_one]
    exact hj
  have hD : ∀ W : Subgroup G, W ≤ Subgroup.centralizer (f5.P₁ : Set G) → IsPGroup 2 W →
      Nat.card W ≤ 2 :=
    Sec54.card_le_two hJC s.orderOf_J hB1
  have hHME : H ≤ M ⊔ s.fr.E := by
    intro h hh
    have hhJ : h * s.J * h⁻¹ ∈ Subgroup.centralizer (f5.P₁ : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (Sec54.mem_normalizer_centralizer hh) s.J).mp hJC
    obtain ⟨c, hc, hcJ⟩ := Sec54.exists_conj hJC s.orderOf_J hD hhJ
    set n := c⁻¹ * h with hndef
    have hnH : n ∈ s.H := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : n * s.J * n⁻¹ = s.J := by
        rw [hndef]
        calc c⁻¹ * h * s.J * (c⁻¹ * h)⁻¹ = c⁻¹ * (h * s.J * h⁻¹) * c := by group
          _ = c⁻¹ * (c * s.J * c⁻¹) * c := by rw [hcJ]
          _ = s.J := by group
      calc n * s.J = n * s.J * n⁻¹ * n := by group
        _ = s.J * n := by rw [h1]
    have hnN : n ∈ H := H.mul_mem (H.inv_mem (Subgroup.centralizer_le_normalizer _ hc)) hh
    obtain ⟨j', hj', m, hm, hnjm⟩ := s.fr.exists_decomp_H_JM hnH
    have hmN : m ∈ H := by
      have h1 : m = j'⁻¹ * n := by rw [hnjm]; group
      rw [h1]
      exact H.mul_mem (H.inv_mem (Subgroup.zpowers_le.mpr
        (Subgroup.centralizer_le_normalizer _ hJC) hj')) hnN
    have hmPBE : m ∈ f5.P₁ ⊔ f5.B ⊔ s.fr.E := by
      rw [← f5.normalizer_eq]
      exact Subgroup.mem_inf.mpr ⟨hmN, hm⟩
    have hle : f5.P₁ ⊔ f5.B ⊔ s.fr.E ≤ M ⊔ s.fr.E :=
      sup_le (sup_le (hP₁C.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans le_sup_left)) le_sup_right
    have hh' : h = c * j' * m := by
      have h1 : h = c * n := by rw [hndef]; group
      rw [h1, hnjm]
      group
    rw [hh']
    refine mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hc)) ?_) (hle hmPBE)
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.zpowers_le.mpr hJC hj'))
  have hcop : ∀ h ∈ H, Nat.Coprime 5 (orderOf h) → h ∈ M := by
    intro h hh hcop
    obtain ⟨m, hm, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEM).mp (hHME hh)
    have hpow : ∀ k : ℕ, ∃ m' ∈ M, (m * e) ^ k = m' * e ^ k := by
      intro k
      induction k with
      | zero => exact ⟨1, M.one_mem, by simp⟩
      | succ k ih =>
        obtain ⟨m', hm', hk⟩ := ih
        refine ⟨m' * (e ^ k * m * (e ^ k)⁻¹), M.mul_mem hm'
          ((Subgroup.mem_normalizer_iff.mp (hEM (s.fr.E.pow_mem he k)) m).mp hm), ?_⟩
        rw [pow_succ, hk]
        group
    obtain ⟨m', hm', hk⟩ := hpow (orderOf (m * e))
    rw [pow_orderOf_eq_one] at hk
    have hek : e ^ orderOf (m * e) ∈ M ⊓ s.fr.E := by
      refine Subgroup.mem_inf.mpr ⟨?_, s.fr.E.pow_mem he _⟩
      rw [eq_inv_of_mul_eq_one_right hk.symm]
      exact M.inv_mem hm'
    rw [hME, Subgroup.mem_bot] at hek
    have hdvd1 : orderOf e ∣ orderOf (m * e) := orderOf_dvd_of_pow_eq_one hek
    have hdvd2 : orderOf e ∣ 5 := hEcard ▸ Subgroup.orderOf_dvd_natCard _ he
    have he1 : orderOf e = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd2 hcop) hdvd1
    rw [orderOf_eq_one_iff.mp he1, mul_one]
    exact hm
  have hresM : BenderSuzuki.External.hallPResidual 5 H ≤ M.subgroupOf H := by
    rw [BenderSuzuki.External.hallPResidual, Subgroup.closure_le]
    intro g hg
    exact Subgroup.mem_subgroupOf.mpr (hcop g g.2 (by rw [Subgroup.orderOf_coe]; exact hg))
  have hxH : x ∈ (BenderSuzuki.External.hallPResidual 5 H).map H.subtype := by
    rw [hres]
    exact hEN hxE
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxH
  exact hxM (Subgroup.mem_subgroupOf.mp (hresM hy))

end CFSG.Walter.W67
