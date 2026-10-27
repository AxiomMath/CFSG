module

public import CFSG.Quasithin.H13.L32A726a
public import CFSG.Quasithin.EmptyFaithful.S153Baum

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H D : Subgroup G}

theorem t_le_h_726 (hc : Ctx726 G T L V H D) : T ≤ H := by
  rw [hc.eq_kt]
  exact le_sup_right

theorem k_le_centralizer_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) :
    oTwoUpper H ≤ Subgroup.centralizer ({d} : Set G) := fun k hk => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hc.d_comm d hdD k hk).symm

theorem d_le_h_726 (hc : Ctx726 G T L V H D) : D ≤ H := hc.d_le.trans (oTwoUpper_le H)

theorem commute_v1_726 (hc : Ctx726 G T L V H D) {h v : G} (hh : h ∈ H) (hv : v ∈ fsuV1 T V) :
    h * v = v * h := by
  rw [hc.eq_hz, L32A.hz] at hh
  exact ((Subgroup.mem_centralizer_iff.mp hh) v hv).symm

theorem conj_d_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V)
    {h : G} (hh : h ∈ H) : d⁻¹ * (h * d * h⁻¹) ∈ fsuV1 T V := by
  have hV2 := card_v1_726 hc hdD hdV
  have hmem : h * d * h⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hc.d_normal hh) d).mp hdD
  have hnot : h * d * h⁻¹ ∉ fsuV1 T V := by
    intro hv
    apply hdV
    have hc' := commute_v1_726 hc (H.inv_mem hh) hv
    have e2 : d = h * d * h⁻¹ := by
      calc d = h⁻¹ * (h * d * h⁻¹) * h := by group
        _ = (h * d * h⁻¹) * h⁻¹ * h := by rw [hc']
        _ = h * d * h⁻¹ := by group
    rw [e2]
    exact hv
  exact inv_mul_mem_v1_726 hc hV2 hdD hdV hmem hnot

theorem commute_conj_iff_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) {h x : G} (hh : h ∈ H) (hx : x ∈ H) :
    x * (h * d * h⁻¹) = (h * d * h⁻¹) * x ↔ x * d = d * x := by
  set v := d⁻¹ * (h * d * h⁻¹) with hv
  have hvV : v ∈ fsuV1 T V := conj_d_726 hc hdD hdV hh
  have e : h * d * h⁻¹ = d * v := by rw [hv]; group
  have hxv : x * v = v * x := commute_v1_726 hc hx hvV
  rw [e]
  constructor
  · intro h1
    have h2 : x * d * v = d * x * v := by
      calc x * d * v = x * (d * v) := by group
        _ = d * v * x := h1
        _ = d * (v * x) := by group
        _ = d * (x * v) := by rw [hxv]
        _ = d * x * v := by group
    exact mul_right_cancel h2
  · intro h1
    calc x * (d * v) = x * d * v := by group
      _ = d * x * v := by rw [h1]
      _ = d * (x * v) := by group
      _ = d * (v * x) := by rw [hxv]
      _ = d * v * x := by group

theorem relIndex_td_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V)
    {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t) :
    ((T ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf T).index = 2 := by
  have hV2 := card_v1_726 hc hdD hdV
  have hTH := t_le_h_726 hc
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨t, htT⟩, fun b => ?_⟩
  have hbH : (b : G) ∈ H := hTH b.2
  have htH : t ∈ H := hTH htT
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  have hvt := conj_d_726 hc hdD hdV htH
  have hvb := conj_d_726 hc hdD hdV hbH
  have hne_t : d⁻¹ * (t * d * t⁻¹) ≠ 1 := by
    intro h
    apply htd
    have : t * d * t⁻¹ = d := by
      calc t * d * t⁻¹ = d * (d⁻¹ * (t * d * t⁻¹)) := by group
        _ = d := by rw [h, mul_one]
    calc t * d = t * d * t⁻¹ * t := by group
      _ = d * t := by rw [this]
  have hiff : ∀ x : G, x ∈ H → (x * d * x⁻¹ = d ↔ x * d = d * x) := fun x _ => by
    constructor
    · intro h
      calc x * d = x * d * x⁻¹ * x := by group
        _ = d * x := by rw [h]
    · intro h
      rw [h]
      group
  have hV1eq : ∀ u ∈ fsuV1 T V, ∀ w ∈ fsuV1 T V, u ≠ 1 → w ≠ 1 → u = w := by
    intro u hu w hw hu1 hw1
    have hz := v1_ne_bot_726 hc
    have hcard := hV2
    by_contra hne
    have h3 : 3 ≤ Nat.card (fsuV1 T V) := by
      classical
      let S : Finset G := {1, u, w}
      have hS : S.card = 3 := by
        simp only [S]
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hu1, Ne.symm hw1]),
          Finset.card_pair hne]
      have hsub : (S : Set G) ⊆ (fsuV1 T V : Set G) := by
        intro x hx
        simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact (fsuV1 T V).one_mem
        · exact hu
        · exact hw
      have hle : Nat.card (S : Set G) ≤ Nat.card (fsuV1 T V : Set G) :=
        Nat.card_mono (Set.toFinite _) hsub
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hS] at hle
      exact hle
    omega
  by_cases hb : (b : G) * d = d * b
  · right
    refine ⟨⟨b.2, hb⟩, fun h => htd ?_⟩
    have h2 := h.2
    have e : (b : G) * t * d = (b : G) * (d * t) := by
      calc (b : G) * t * d = d * (b * t) := h2
        _ = d * b * t := by group
        _ = b * d * t := by rw [hb]
        _ = (b : G) * (d * t) := by group
    rw [mul_assoc] at e
    exact mul_left_cancel e
  · left
    refine ⟨⟨T.mul_mem b.2 htT, ?_⟩, fun h => hb h.2⟩
    have hne_b : d⁻¹ * ((b : G) * d * (b : G)⁻¹) ≠ 1 := by
      intro h
      apply hb
      have : (b : G) * d * (b : G)⁻¹ = d := by
        calc (b : G) * d * (b : G)⁻¹ = d * (d⁻¹ * ((b : G) * d * (b : G)⁻¹)) := by group
          _ = d := by rw [h, mul_one]
      exact (hiff b hbH).mp this
    have huw := hV1eq _ hvb _ hvt hne_b hne_t
    set u := d⁻¹ * (t * d * t⁻¹) with hu
    have hu2 : u * u = 1 := (mem_v1_726 hvt).1
    have hbu : (b : G) * u * (b : G)⁻¹ = u := by
      rw [commute_v1_726 hc hbH hvt]
      group
    refine (hiff _ (H.mul_mem hbH htH)).mp ?_
    calc (b : G) * t * d * ((b : G) * t)⁻¹ = (b : G) * (t * d * t⁻¹) * (b : G)⁻¹ := by group
      _ = (b : G) * (d * u) * (b : G)⁻¹ := by rw [hu]; group
      _ = ((b : G) * d * (b : G)⁻¹) * ((b : G) * u * (b : G)⁻¹) := by group
      _ = (d * (d⁻¹ * ((b : G) * d * (b : G)⁻¹))) * u := by rw [hbu]; group
      _ = d * u * u := by rw [huw]
      _ = d := by rw [mul_assoc, hu2, mul_one]

theorem t_le_normalizer_k_726 (hc : Ctx726 G T L V H D) :
    T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
  (t_le_h_726 hc).trans (le_normalizer_oTwoUpper H)

theorem hd_normal_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V) :
    H ≤ Subgroup.normalizer ((H ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) := by
  have key : ∀ h ∈ H, ∀ x ∈ H ⊓ Subgroup.centralizer ({d} : Set G),
      h * x * h⁻¹ ∈ H ⊓ Subgroup.centralizer ({d} : Set G) := by
    intro h hh x hx
    obtain ⟨hxH, hxd⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxd ⊢
    have h1 := (commute_conj_iff_726 hc hdD hdV (H.inv_mem hh) hxH).mpr hxd
    rw [inv_inv] at h1
    calc h * x * h⁻¹ * d = h * (x * (h⁻¹ * d * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * d * h) * x) * h⁻¹ := by rw [h1]
      _ = d * (h * x * h⁻¹) := by group
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key h hh x, fun hx => ?_⟩
  have := key h⁻¹ (H.inv_mem hh) _ hx
  simpa [mul_assoc] using this

theorem isSylowTwoOf_top_726 (hc : Ctx726 G T L V H D) : IsSylowTwoOf T ⊤ := by
  obtain ⟨h2, hodd⟩ := hc.setting.hyp.hyp.h13.sylow
  refine ⟨le_top, h2, ?_⟩
  rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  exact hodd

theorem isSylowTwoOf_h_726 (hc : Ctx726 G T L V H D) : IsSylowTwoOf T H := by
  obtain ⟨h2, hodd⟩ := hc.setting.hyp.hyp.h13.sylow
  refine ⟨t_le_h_726 hc, h2, fun h => hodd ?_⟩
  exact h.trans (Subgroup.relIndex_dvd_index_of_le (t_le_h_726 hc))

theorem isSylowTwoOf_td_hd_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({d} : Set G))
      (H ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have h := A4.isSylowTwoOf_inf_normal (isSylowTwoOf_h_726 hc) inf_le_left
    (hd_normal_726 hc hdD hdV)
  rwa [← inf_assoc, inf_eq_left.mpr (t_le_h_726 hc)] at h

theorem charTwo_h_726 (hc : Ctx726 G T L V H D) : CharTwo H :=
  charTwo_of_isTwoLocal_of_isSylowTwoOf_le hc.setting.hyp.hyp.h13.qtke.2.1
    (isSylowTwoOf_top_726 hc) hc.max_two_local.1 (t_le_h_726 hc)

theorem charTwo_hd_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V) :
    CharTwo (H ⊓ Subgroup.centralizer ({d} : Set G)) :=
  CT.CharTwo.of_normal (charTwo_h_726 hc) inf_le_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr (hd_normal_726 hc hdD hdV))

omit [Finite G] in
theorem commute_of_odd_726 {a k : G} (hk : Odd (orderOf k))
    (hck : a * k * a⁻¹ * k⁻¹ * k = k * (a * k * a⁻¹ * k⁻¹))
    (hc2 : ∃ e : ℕ, (a * k * a⁻¹ * k⁻¹) ^ 2 ^ e = 1) : a * k = k * a := by
  set c := a * k * a⁻¹ * k⁻¹ with hc
  have hcomm : Commute k c := hck.symm
  have hstep : k * a⁻¹ * k⁻¹ = a⁻¹ * c := by rw [hc]; group
  have hpow : ∀ n : ℕ, k ^ n * a⁻¹ * (k ^ n)⁻¹ = a⁻¹ * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc k ^ (n + 1) * a⁻¹ * (k ^ (n + 1))⁻¹ = k * (k ^ n * a⁻¹ * (k ^ n)⁻¹) * k⁻¹ := by
            rw [pow_succ']
            group
        _ = k * (a⁻¹ * c ^ n) * k⁻¹ := by rw [ih]
        _ = (k * a⁻¹ * k⁻¹) * (k * c ^ n * k⁻¹) := by group
        _ = (a⁻¹ * c) * c ^ n := by
            rw [hstep, (hcomm.pow_right n).eq, mul_inv_cancel_right]
        _ = a⁻¹ * c ^ (n + 1) := by rw [pow_succ']; group
  have hcm : c ^ orderOf k = 1 := by
    have h := hpow (orderOf k)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h
    have := congrArg (fun x => a * x) h
    simpa using this.symm
  obtain ⟨e, he⟩ := hc2
  have h1 : orderOf c ∣ Nat.gcd (orderOf k) (2 ^ e) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcm) (orderOf_dvd_of_pow_eq_one he)
  have hcop : Nat.gcd (orderOf k) (2 ^ e) = 1 :=
    Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hk)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
  have h2 : a * k * a⁻¹ * k⁻¹ = 1 := h1
  calc a * k = a * k * a⁻¹ * k⁻¹ * (k * a) := by group
    _ = k * a := by rw [h2, one_mul]

omit [Finite G] in
theorem normalizer_le_normalizer_center_726 (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer ((X ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G),
      ∀ x ∈ X ⊓ Subgroup.centralizer (X : Set G),
      g * x * g⁻¹ ∈ X ⊓ Subgroup.centralizer (X : Set G) := by
    intro g hg x hx
    obtain ⟨hxX, hxc⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxX, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : g⁻¹ * y * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
      simpa using this
    have h1 := (Subgroup.mem_centralizer_iff.mp hxc) _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * y := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem k_le_centralizer_center_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) :
    oTwoUpper H ≤ Subgroup.centralizer
      ((pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set G)) ⊓
        Subgroup.centralizer (pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set G)) : Set G) :
          Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Hd := H ⊓ Subgroup.centralizer ({d} : Set G) with hHd
  set Q := pCoreOf 2 Hd with hQ
  set K := oTwoUpper H with hK
  have hKHd : K ≤ Hd := le_inf (oTwoUpper_le H) (k_le_centralizer_726 hc hdD)
  have hQHd : Q ≤ Hd := pCoreOf_le 2 Hd
  have hHdQ : Hd ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 Hd
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hPQ : pCoreOf 2 K ≤ Q :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKHd)
      ((inf_le_left.trans hHK).trans (normalizer_le_normalizer_pCoreOf 2 K))
      (pCoreOf_isPGroup 2 K)
  have hKQP : K ⊓ Q ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, hHdQ (hKHd hx)⟩)
      ((pCoreOf_isPGroup 2 Hd).to_le inf_le_right)
  rw [hK, oTwoUpper]
  rw [Subgroup.closure_le]
  rintro x ⟨hxH, hxodd⟩
  have hxK : x ∈ K := Subgroup.subset_closure ⟨hxH, hxodd⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨haQ, hac⟩ := Subgroup.mem_inf.mp ha
  have haH : a ∈ H := (hQHd haQ).1
  have hcK : a * x * a⁻¹ * x⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHK haH) x).mp hxK) (K.inv_mem hxK)
  have hxN : x ∈ Subgroup.normalizer (Q : Set G) := hHdQ (hKHd hxK)
  have hcQ : a * x * a⁻¹ * x⁻¹ ∈ Q := by
    have h1 : x * a⁻¹ * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxN _).mp (Q.inv_mem haQ)
    have e : a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact Q.mul_mem haQ h1
  have hcc : a * x * a⁻¹ * x⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : x⁻¹ * q * x ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) q).mp hq
      simpa using this
    have h1 := (Subgroup.mem_centralizer_iff.mp hac) q hq
    have h2 := (Subgroup.mem_centralizer_iff.mp hac) _ hq'
    have h3 : x * a⁻¹ * x⁻¹ * q = q * (x * a⁻¹ * x⁻¹) := by
      have h4 : a⁻¹ * (x⁻¹ * q * x) = (x⁻¹ * q * x) * a⁻¹ :=
        (Commute.inv_right (show Commute (x⁻¹ * q * x) a from h2)).eq.symm
      calc x * a⁻¹ * x⁻¹ * q = x * (a⁻¹ * (x⁻¹ * q * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * q * x) * a⁻¹) * x⁻¹ := by rw [h4]
        _ = q * (x * a⁻¹ * x⁻¹) := by group
    calc q * (a * x * a⁻¹ * x⁻¹) = q * a * (x * a⁻¹ * x⁻¹) := by group
      _ = a * q * (x * a⁻¹ * x⁻¹) := by rw [h1]
      _ = a * (q * (x * a⁻¹ * x⁻¹)) := by group
      _ = a * (x * a⁻¹ * x⁻¹ * q) := by rw [h3]
      _ = a * x * a⁻¹ * x⁻¹ * q := by group
  have hcP : a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 K := hKQP ⟨hcK, hcQ⟩
  have hcZ : ∀ y ∈ pCoreOf 2 K, a * x * a⁻¹ * x⁻¹ * y = y * (a * x * a⁻¹ * x⁻¹) := fun y hy =>
    ((Subgroup.mem_centralizer_iff.mp hcc) y (hPQ hy)).symm
  have hck := hc.center_p _ hcP hcZ x hxK
  have hc2 : ∃ e : ℕ, (a * x * a⁻¹ * x⁻¹) ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := pCoreOf_isPGroup 2 Hd ⟨_, hcQ⟩
    exact ⟨e, congrArg Subtype.val he⟩
  exact commute_of_odd_726 hxodd hck hc2

theorem le_normalizer_center_td_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t) :
    H ≤ Subgroup.normalizer
      (((T ⊓ Subgroup.centralizer ({d} : Set G)) ⊓
        Subgroup.centralizer ((T ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) :
          Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Td := T ⊓ Subgroup.centralizer ({d} : Set G) with hTd
  set Hd := H ⊓ Subgroup.centralizer ({d} : Set G) with hHd
  have hsyl := isSylowTwoOf_td_hd_726 hc hdD hdV
  have hQTd : pCoreOf 2 Hd ≤ Td := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsyl
  have hZ : Td ⊓ Subgroup.centralizer (Td : Set G) ≤
      pCoreOf 2 Hd ⊓ Subgroup.centralizer (pCoreOf 2 Hd : Set G) := by
    intro y hy
    obtain ⟨hyT, hyc⟩ := Subgroup.mem_inf.mp hy
    have hyC : y ∈ Subgroup.centralizer (pCoreOf 2 Hd : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQTd) hyc
    exact Subgroup.mem_inf.mpr ⟨charTwo_hd_726 hc hdD hdV ⟨hsyl.1 hyT, hyC⟩, hyC⟩
  have hKZ : oTwoUpper H ≤ Subgroup.normalizer
      ((Td ⊓ Subgroup.centralizer (Td : Set G) : Subgroup G) : Set G) :=
    ((k_le_centralizer_center_726 hc hdD).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZ))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hidx := relIndex_td_726 hc hdD hdV htT htd
  have hnormal : (Td.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hidx
  have hTTd : T ≤ Subgroup.normalizer (Td : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hnormal
  rw [hc.eq_kt]
  exact sup_le hKZ (hTTd.trans (normalizer_le_normalizer_center_726 Td))

theorem normalizer_td_le_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t) :
    Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) ≤ H := by
  set Td := T ⊓ Subgroup.centralizer ({d} : Set G) with hTd
  set Z := Td ⊓ Subgroup.centralizer (Td : Set G) with hZdef
  have hZ1 : Z ≠ ⊥ := by
    obtain ⟨⟨v, hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (v1_ne_bot_726 hc)
    have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hvT : v ∈ T := (mem_omegaOneCenter_726 (Subgroup.mem_inf.mp hvV).2).1
    have hvd : v ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_v1_726 hc (d_le_h_726 hc hdD) hvV).symm
    have hvZ : v ∈ Z := by
      refine Subgroup.mem_inf.mpr ⟨⟨hvT, hvd⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact (mem_v1_726 hvV).2 s (Subgroup.mem_inf.mp hs).1
    intro h
    exact hv1' (by rw [h] at hvZ; exact Subgroup.mem_bot.mp hvZ)
  have hZ2 : IsPGroup 2 Z :=
    hc.setting.hyp.hyp.h13.sylow.1.to_le (inf_le_left.trans inf_le_left)
  have hloc : IsTwoLocal (Subgroup.normalizer (Z : Set G)) := ⟨Z, hZ1, hZ2, rfl⟩
  have hHZ := le_normalizer_center_td_726 hc hdD hdV htT htd
  rw [← hc.max_two_local.2 _ hloc hHZ]
  exact normalizer_le_normalizer_center_726 Td

theorem isSylowTwoOf_td_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({d} : Set G)) (Subgroup.centralizer ({d} : Set G)) := by
  refine isSylowTwoOf_of_normalizer_le inf_le_right (normalizer_td_le_726 hc hdD hdV htT htd) ?_
  rw [inf_comm (Subgroup.centralizer ({d} : Set G)) H]
  exact isSylowTwoOf_td_hd_726 hc hdD hdV

theorem not_conj_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) {t : G} (htT : t ∈ T) (htd : t * d ≠ d * t) :
    ∀ g : G, ∀ v ∈ fsuV1 T V, g * v * g⁻¹ ≠ d := by
  intro g v hv hgv
  have hsyl := isSylowTwoOf_td_726 hc hdD hdV htT htd
  set Td := T ⊓ Subgroup.centralizer ({d} : Set G) with hTd
  have hTg : conjByElt g T ≤ Subgroup.centralizer ({d} : Set G) := by
    intro x hx
    rw [mem_conjByElt] at hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgv]
    have h1 := (mem_v1_726 hv).2 _ hx
    calc x * (g * v * g⁻¹) = g * ((g⁻¹ * x * g) * v) * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * v * g⁻¹ * x := by group
  have hT2 : IsPGroup 2 (conjByElt g T) := hc.setting.hyp.hyp.h13.sylow.1.map _
  have hle : Nat.card (conjByElt g T) ≤ Nat.card Td := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hT2
    have hdvdK : Nat.card (conjByElt g T) ∣ Nat.card (Subgroup.centralizer ({d} : Set G)) :=
      Subgroup.card_dvd_of_le hTg
    have hK : Nat.card (Subgroup.centralizer ({d} : Set G)) =
        Nat.card Td * (Td.subgroupOf (Subgroup.centralizer ({d} : Set G))).index := by
      rw [← Subgroup.relIndex, ← Subgroup.relIndex_mul_card, mul_comm,
        inf_of_le_left hsyl.1]
    rw [hK, ha] at hdvdK
    have hcop : Nat.Coprime (2 ^ a) (Td.subgroupOf (Subgroup.centralizer ({d} : Set G))).index :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hsyl.2.2)
    rw [ha]
    exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hdvdK)
  have hidx := relIndex_td_726 hc hdD hdV htT htd
  have hTd2 : Nat.card T = Nat.card Td * 2 := by
    rw [← hidx, ← Subgroup.relIndex, ← Subgroup.relIndex_mul_card, mul_comm,
      inf_of_le_left inf_le_left]
  have hcardg : Nat.card (conjByElt g T) = Nat.card T := by
    rw [conjByElt, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hpos : 0 < Nat.card Td := Nat.card_pos
  omega

theorem fusionIsTI_of_centralizer_le_726 (hc : Ctx726 G T L V H D)
    (hmain : ∀ d ∈ D, d ∉ fsuV1 T V → d * d = 1 → ∀ t ∈ T, t * d ≠ d * t →
      Subgroup.centralizer ({d} : Set G) ≤ H) : fusionIsTI D :=
  fusionIsTI_of_main_726 hc fun d hdD hdV hd2 ⟨t, htT, htd⟩ =>
    ⟨hmain d hdD hdV hd2 t htT htd, not_conj_726 hc hdD hdV htT htd⟩

end CFSG.Quasithin.H13.L32A
