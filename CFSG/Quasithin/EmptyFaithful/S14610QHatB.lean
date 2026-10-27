module

public import CFSG.Quasithin.EmptyFaithful.S14610Hat6
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

private theorem mem_pCore_two_iff {K : Subgroup G} (c : ↥K) :
    c ∈ CFSG.pCore 2 ↥K ↔ (c : G) ∈ pCoreOf 2 K := (CFSG.mem_openPCoreOf_iff c).symm

private theorem le_normalizer_blockU_of (K : Subgroup G) :
    K ≤ Subgroup.normalizer (blockU K : Set G) := fun _ hg =>
  A4.mem_normalizer_commutator (le_normalizer_pCoreOf 2 K hg) (Subgroup.le_normalizer hg)

private theorem exists_commSubgroup {K U Q : Subgroup G} {x : G}
    (hUQ : U ≤ Q) (hUC : U ≤ Subgroup.centralizer (Q : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) (hxK : x ∈ K)
    (hxc : ∀ w ∈ K, x * w * x⁻¹ * w⁻¹ ∈ Q) :
    ∃ E : Subgroup G, (∀ c : G, c ∈ E ↔ ∃ u ∈ U, c = x * u * x⁻¹ * u⁻¹) ∧ E ≤ U ∧
      K ≤ Subgroup.normalizer (E : Set G) := by
  have hab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hUC ha) b (hUQ hb)).symm
  have hx : ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (hKU hxK) u).mp hu
  let E : Subgroup G :=
    { carrier := {c | ∃ u ∈ U, c = x * u * x⁻¹ * u⁻¹}
      one_mem' := ⟨1, U.one_mem, by group⟩
      mul_mem' := by
        rintro _ _ ⟨u₁, hu₁, rfl⟩ ⟨u₂, hu₂, rfl⟩
        refine ⟨u₁ * u₂, U.mul_mem hu₁ hu₂, ?_⟩
        have h1 : u₁⁻¹ * (x * u₂ * x⁻¹) = (x * u₂ * x⁻¹) * u₁⁻¹ :=
          hab _ (U.inv_mem hu₁) _ (hx _ hu₂)
        have h2 : u₁⁻¹ * u₂⁻¹ = u₂⁻¹ * u₁⁻¹ := hab _ (U.inv_mem hu₁) _ (U.inv_mem hu₂)
        calc x * u₁ * x⁻¹ * u₁⁻¹ * (x * u₂ * x⁻¹ * u₂⁻¹)
            = x * u₁ * x⁻¹ * (u₁⁻¹ * (x * u₂ * x⁻¹)) * u₂⁻¹ := by group
          _ = x * u₁ * x⁻¹ * ((x * u₂ * x⁻¹) * u₁⁻¹) * u₂⁻¹ := by rw [h1]
          _ = x * u₁ * x⁻¹ * (x * u₂ * x⁻¹) * (u₁⁻¹ * u₂⁻¹) := by group
          _ = x * u₁ * x⁻¹ * (x * u₂ * x⁻¹) * (u₂⁻¹ * u₁⁻¹) := by rw [h2]
          _ = x * (u₁ * u₂) * x⁻¹ * (u₁ * u₂)⁻¹ := by group
      inv_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        refine ⟨u⁻¹, U.inv_mem hu, ?_⟩
        have h : (x * u * x⁻¹)⁻¹ * u = u * (x * u * x⁻¹)⁻¹ :=
          hab _ (U.inv_mem (hx _ hu)) _ hu
        calc (x * u * x⁻¹ * u⁻¹)⁻¹ = u * (x * u * x⁻¹)⁻¹ := by group
          _ = (x * u * x⁻¹)⁻¹ * u := h.symm
          _ = x * u⁻¹ * x⁻¹ * u⁻¹⁻¹ := by group }
  have hE : ∀ c : G, c ∈ E ↔ ∃ u ∈ U, c = x * u * x⁻¹ * u⁻¹ := fun c => Iff.rfl
  have key : ∀ g ∈ K, ∀ c ∈ E, g * c * g⁻¹ ∈ E := by
    intro g hg c hc
    obtain ⟨u, hu, rfl⟩ := (hE c).mp hc
    have hu' : g * u * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hKU hg) u).mp hu
    have hq : g * x * g⁻¹ * x⁻¹ ∈ Q := by
      have h := Q.inv_mem (hxc g hg)
      have e : (x * g * x⁻¹ * g⁻¹)⁻¹ = g * x * g⁻¹ * x⁻¹ := by group
      rwa [e] at h
    have ha : x * (g * u * g⁻¹) * x⁻¹ ∈ U := hx _ hu'
    have hcomm : (g * x * g⁻¹ * x⁻¹) * (x * (g * u * g⁻¹) * x⁻¹) =
        (x * (g * u * g⁻¹) * x⁻¹) * (g * x * g⁻¹ * x⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hUC ha) _ hq
    refine (hE _).mpr ⟨g * u * g⁻¹, hu', ?_⟩
    calc g * (x * u * x⁻¹ * u⁻¹) * g⁻¹
        = (g * x * g⁻¹ * x⁻¹) * (x * (g * u * g⁻¹) * x⁻¹) * (g * x * g⁻¹ * x⁻¹)⁻¹ *
            (g * u * g⁻¹)⁻¹ := by group
      _ = (x * (g * u * g⁻¹) * x⁻¹) * (g * x * g⁻¹ * x⁻¹) * (g * x * g⁻¹ * x⁻¹)⁻¹ *
            (g * u * g⁻¹)⁻¹ := by rw [hcomm]
      _ = x * (g * u * g⁻¹) * x⁻¹ * (g * u * g⁻¹)⁻¹ := by group
  refine ⟨E, hE, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact U.mul_mem (hx u hu) (U.inv_mem hu)
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => key g hg c hc, fun hc => ?_⟩
    have h := key g⁻¹ (K.inv_mem hg) _ hc
    have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
    rwa [e] at h

private theorem comm_eq_one_of_commute {x v : G} (hodd : Odd (orderOf x))
    (h2 : (x * v * x⁻¹ * v⁻¹) ^ 2 = 1)
    (hc : x * (x * v * x⁻¹ * v⁻¹) = (x * v * x⁻¹ * v⁻¹) * x) :
    x * v * x⁻¹ * v⁻¹ = 1 := by
  set u : G := x * v * x⁻¹ * v⁻¹ with hu
  have hxu : x * u * x⁻¹ = u := by rw [hc]; group
  have hxv : x * v * x⁻¹ = u * v := by rw [hu]; group
  have h1 : ∀ i : ℕ, x ^ i * v * (x ^ i)⁻¹ = u ^ i * v := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e1 : x ^ (i + 1) * v * (x ^ (i + 1))⁻¹ = x * (x ^ i * v * (x ^ i)⁻¹) * x⁻¹ := by
        rw [pow_succ']; group
      have e2 : x * (u ^ i * v) * x⁻¹ = (x * u * x⁻¹) ^ i * (x * v * x⁻¹) := by
        rw [conj_pow]; group
      rw [e1, ih, e2, hxu, hxv, pow_succ]
      group
  have h3 : u ^ orderOf x = 1 := by
    have h := h1 (orderOf x)
    rw [pow_orderOf_eq_one] at h
    have h' : v = u ^ orderOf x * v := by simpa using h
    exact (mul_eq_right.mp h'.symm)
  obtain ⟨m, hm⟩ := hodd
  rw [hm] at h3
  calc u = u ^ (2 * m) * u := by rw [pow_mul, h2, one_pow, one_mul]
    _ = u ^ (2 * m + 1) := by rw [pow_succ]
    _ = 1 := h3

private theorem wOf1469_le_blockU (K : Subgroup G) : wOf1469 K ≤ blockU K :=
  Subgroup.commutator_mono ((Subgroup.closure_le _).mpr fun _ hx => hx.1.1) le_rfl

private theorem mk_mem_center_of_mem_oTwoZIn {K : Subgroup G} {x : G} (hx : x ∈ oTwoZIn K) :
    ∃ hxK : x ∈ K, (QuotientGroup.mk ⟨x, hxK⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
  unfold oTwoZIn preimageModTwoCore at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact ⟨y.2, Subgroup.mem_comap.mp hy⟩

private theorem exists_odd_oTwoZIn [Finite G] (K : Subgroup G)
    (hcard : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3) :
    ∃ x ∈ oTwoZIn K, Odd (orderOf x) ∧ x ∉ pCoreOf 2 K := by
  have h1 : 1 < Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) := by omega
  have : Nontrivial ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨c, hc⟩ := exists_ne (1 : ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (c : ↥K ⧸ CFSG.pCore 2 ↥K)
  have hc3 : orderOf (c : ↥K ⧸ CFSG.pCore 2 ↥K) = 3 := by
    have hd : orderOf c ∣ 3 := hcard ▸ orderOf_dvd_natCard c
    have hne : orderOf c ≠ 1 := fun h => hc (orderOf_eq_one_iff.mp h)
    rw [Subgroup.orderOf_coe]
    exact ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hne
  have hpos : 0 < orderOf k := orderOf_pos k
  obtain ⟨j, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  have hord : orderOf (k ^ 2 ^ j) = m := by
    rw [orderOf_pow_of_dvd (by positivity) ⟨m, hn⟩, hn]
    exact Nat.mul_div_cancel_left m (by positivity)
  have hmk : (QuotientGroup.mk (k ^ 2 ^ j) : ↥K ⧸ CFSG.pCore 2 ↥K) =
      (c : ↥K ⧸ CFSG.pCore 2 ↥K) ^ 2 ^ j := by
    rw [QuotientGroup.mk_pow, hk]
  refine ⟨((k ^ 2 ^ j : ↥K) : G), ?_, ?_, ?_⟩
  · unfold oTwoZIn preimageModTwoCore
    refine Subgroup.mem_map.mpr ⟨k ^ 2 ^ j, Subgroup.mem_comap.mpr ?_, rfl⟩
    show (QuotientGroup.mk (k ^ 2 ^ j) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ _
    rw [hmk]
    exact Subgroup.pow_mem _ c.2 _
  · rw [Subgroup.orderOf_coe, hord]
    exact hm
  · rw [← mem_pCore_two_iff, ← QuotientGroup.eq_one_iff, hmk]
    intro h
    have h3 : (3 : ℕ) ∣ 2 ^ j := hc3 ▸ orderOf_dvd_iff_pow_eq_one.mpr h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

private theorem exists_action {K E : Subgroup G} (hEK : E ≤ K)
    (hn : K ≤ Subgroup.normalizer (E : Set G))
    (htriv : ∀ q ∈ pCoreOf 2 K, ∀ e ∈ E, q * e * q⁻¹ = e) :
    ∃ φ : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut ↥(E.subgroupOf K),
      ∀ (k : ↥K) (e : ↥(E.subgroupOf K)),
        (((φ (QuotientGroup.mk k)) e : ↥(E.subgroupOf K)) : ↥K) = k * (e : ↥K) * k⁻¹ := by
  have : (E.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hEK).mpr hn
  have hker : CFSG.pCore 2 ↥K ≤
      (MulAut.conjNormal : ↥K →* MulAut ↥(E.subgroupOf K)).ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun e => ?_
    rw [MulAut.one_apply]
    refine Subtype.ext (Subtype.ext ?_)
    have h := htriv (q : G) ((mem_pCore_two_iff q).mp hq) ((e : ↥K) : G)
      (Subgroup.mem_subgroupOf.mp e.2)
    simpa using h
  refine ⟨QuotientGroup.lift _ MulAut.conjNormal hker, fun k e => ?_⟩
  rw [QuotientGroup.lift_mk, MulAut.conjNormal_apply]

theorem input14610Hat6_of_small_action
    (hA : ∀ (Q : Type) [Group Q] [Finite Q], Group.IsPerfect Q →
      IsSimpleGroup (Q ⧸ Subgroup.center Q) → Nat.card (Subgroup.center Q) = 3 →
      Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) →
      ∀ (E : Type) [Group E] [Finite E] [Nontrivial E], (∃ d : ℕ, Nat.card E = 2 ^ d) →
        Nat.card E ≤ 2 ^ 5 → ∀ (φ : Q →* MulAut E) (z : Q), z ∈ Subgroup.center Q → z ≠ 1 →
          (∀ e : E, φ z e = e → e = 1) → False) :
    Input14610Hat6 := by
  intro G _ _ K hHat
  obtain ⟨⟨-, -, ⟨hUle, hU2⟩, -, -⟩, hhat, hcardU, hcentU⟩ := hHat
  have hUQ : blockU K ≤ pCoreOf 2 K := hUle.trans inf_le_left
  have hUC : blockU K ≤ Subgroup.centralizer (pCoreOf 2 K : Set G) := hUle.trans inf_le_right
  obtain ⟨x, hxZ, hxodd, hxQ⟩ := exists_odd_oTwoZIn K hhat.2.1
  obtain ⟨hxK, hxc⟩ := mem_oTwoZIn_iff_commutator.mp hxZ
  obtain ⟨E, hE, hEU, hEn⟩ := exists_commSubgroup hUQ hUC (le_normalizer_blockU_of K) hxK hxc
  have hEK : E ≤ K := (hEU.trans hUQ).trans (pCoreOf_le 2 K)
  obtain ⟨u₀, hu₀, hu₀x⟩ : ∃ u ∈ blockU K, u * x ≠ x * u := by
    by_contra h
    have hxC : x ∈ Subgroup.centralizer (blockU K : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun u hu => by_contra fun hne => h ⟨u, hu, hne⟩
    exact hxQ (hcentU ▸ ⟨hxK, hxC⟩)
  have hfix : ∀ e ∈ E, x * e * x⁻¹ = e → e = 1 := by
    intro e he hxe
    obtain ⟨u, hu, rfl⟩ := (hE e).mp he
    refine comm_eq_one_of_commute hxodd (hU2 _ (hEU he)) ?_
    calc x * (x * u * x⁻¹ * u⁻¹) = x * (x * u * x⁻¹ * u⁻¹) * x⁻¹ * x := by group
      _ = (x * u * x⁻¹ * u⁻¹) * x := by rw [hxe]
  rw [eq_bot_iff]
  rintro w ⟨hwW, hwC⟩
  rw [Subgroup.mem_bot]
  by_contra hw1
  have hxX : x ∈ oTwoUpper (oTwoZIn K) := mem_oTwoUpper_of_odd hxZ hxodd
  have hxw : x * w * x⁻¹ = w := by
    rw [Subgroup.mem_centralizer_iff.mp hwC x hxX]
    group
  have hEne : E ≠ blockU K := fun h => hw1 (hfix w (h ▸ wOf1469_le_blockU K hwW) hxw)
  have hc₀E : x * u₀ * x⁻¹ * u₀⁻¹ ∈ E := (hE _).mpr ⟨u₀, hu₀, rfl⟩
  have hc₀ : x * u₀ * x⁻¹ * u₀⁻¹ ≠ 1 := by
    intro h
    apply hu₀x
    have h' : x * u₀ = (x * u₀ * x⁻¹ * u₀⁻¹) * (u₀ * x) := by group
    rw [h, one_mul] at h'
    exact h'.symm
  have hEcard : Nat.card E ∣ 2 ^ 6 := hcardU ▸ Subgroup.card_dvd_of_le hEU
  obtain ⟨d, -, hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hEcard
  have hd5 : d ≤ 5 := by
    by_contra hcon
    have hd6 : d = 6 := by
      have : d ≤ 6 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hd ▸ hEcard)
      omega
    exact hEne (Subgroup.eq_of_le_of_card_ge hEU (by rw [hcardU, hd, hd6]))
  have hE'card : Nat.card ↥(E.subgroupOf K) = 2 ^ d :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv).trans hd
  have : Nontrivial ↥(E.subgroupOf K) :=
    nontrivial_of_ne (⟨⟨_, hEK hc₀E⟩, Subgroup.mem_subgroupOf.mpr hc₀E⟩ : ↥(E.subgroupOf K)) 1
      fun h => hc₀ (congrArg (fun a : ↥(E.subgroupOf K) => ((a : ↥K) : G)) h)
  obtain ⟨φ, hφ⟩ := exists_action hEK hEn fun q hq e he =>
    by rw [(Subgroup.mem_centralizer_iff.mp (hUC (hEU he)) q hq)]; group
  obtain ⟨_, hz⟩ := mk_mem_center_of_mem_oTwoZIn hxZ
  refine hA _ hhat.1.1 hhat.1.2.1 hhat.2.1 hhat.2.2 ↥(E.subgroupOf K) ⟨d, hE'card⟩
    (by rw [hE'card]; exact Nat.pow_le_pow_right (by norm_num) hd5) φ
    (QuotientGroup.mk ⟨x, hxK⟩) hz
    (fun h => hxQ ((mem_pCore_two_iff _).mp ((QuotientGroup.eq_one_iff _).mp h))) ?_
  intro e he
  have h1 := hφ ⟨x, hxK⟩ e
  rw [he] at h1
  have h2 : x * ((e : ↥K) : G) * x⁻¹ = ((e : ↥K) : G) := by
    simpa using (congrArg (fun a : ↥K => (a : G)) h1).symm
  exact Subtype.ext (Subtype.ext (hfix _ (Subgroup.mem_subgroupOf.mp e.2) h2))

end CFSG.Quasithin
