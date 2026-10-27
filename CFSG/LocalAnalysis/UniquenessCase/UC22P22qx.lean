module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qu

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22qx_Q_conj {p : ℕ} {M : Subgroup G} {m q : G} (hm : m ∈ M)
    (hq : q ∈ uniqueFourPrimeCore p M) : m * q * m⁻¹ ∈ uniqueFourPrimeCore p M :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_conj_mem hq hm

theorem uc22p22qx_conj_le {p : ℕ} [Fact p.Prime] {M P₁ Dd : Subgroup G} (hP₁M : P₁ ≤ M) (hP₁ : IsPGroup p P₁)
    (hYn : M ≤ normalizer ((P₁ ⊔ uniqueFourPrimeCore p M : Subgroup G) : Set G))
    (hQ : ∀ q ∈ uniqueFourPrimeCore p M, ∃ r ∈ pCoreOf 2 M, ∃ d ∈ Dd, q = r * d)
    (hDP : ∀ d ∈ Dd, ∀ a ∈ P₁, d * a = a * d) :
    ∀ m ∈ M, ∀ x ∈ P₁, m * x * m⁻¹ ∈ P₁ ⊔ pCoreOf 2 M := by
  intro m hm x hx
  have hS : IsSylowOf p P₁ (P₁ ⊔ uniqueFourPrimeCore p M) := uc22p22qu_isSylowOf_sup hP₁M hP₁
  obtain ⟨y, hy, hn⟩ := uc22p22qq_frattini hS
    (fun m hm y hy => (mem_normalizer_iff.1 (hYn hm) y).1 hy) m hm
  have hP₁Q : P₁ ≤ normalizer (uniqueFourPrimeCore p M : Set G) := fun a ha =>
    uc22p22qk_mem_normalizer fun q hq => uc22p22qx_Q_conj (hP₁M ha) hq
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hP₁Q] at hy
  obtain ⟨q, hq, a, ha, rfl⟩ := hy
  obtain ⟨r, hr, d, hd, rfl⟩ := hQ q hq
  generalize hnd : (r * d * a)⁻¹ * m = n at hn
  have hm' : m = r * d * a * n := by rw [← hnd]; group
  have hx₁ : n * x * n⁻¹ ∈ P₁ := (mem_normalizer_iff.1 hn x).1 hx
  have hx' : a * (n * x * n⁻¹) * a⁻¹ ∈ P₁ := P₁.mul_mem (P₁.mul_mem ha hx₁) (P₁.inv_mem ha)
  set x' : G := a * (n * x * n⁻¹) * a⁻¹ with hx'def
  have hdx : d * x' * d⁻¹ = x' := by rw [hDP d hd x' hx']; group
  have hR : r * (x' * r⁻¹ * x'⁻¹) ∈ pCoreOf 2 M :=
    (pCoreOf 2 M).mul_mem hr (uc22p22qh_conj_mem_pCoreOf (hP₁M hx') ((pCoreOf 2 M).inv_mem hr))
  have e : m * x * m⁻¹ = (r * (x' * r⁻¹ * x'⁻¹)) * x' := by
    calc m * x * m⁻¹ = r * (d * x' * d⁻¹) * r⁻¹ := by rw [hm', hx'def]; group
      _ = r * x' * r⁻¹ := by rw [hdx]
      _ = _ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hR) (Subgroup.mem_sup_left hx')

theorem uc22p22qx_normalizes {M P₁ : Subgroup G}
    (h : ∀ m ∈ M, ∀ x ∈ P₁, m * x * m⁻¹ ∈ P₁ ⊔ pCoreOf 2 M) :
    M ≤ normalizer ((P₁ ⊔ pCoreOf 2 M : Subgroup G) : Set G) := by
  intro m hm
  have hmap : (P₁ ⊔ pCoreOf 2 M).map (MulAut.conj m).toMonoidHom ≤ P₁ ⊔ pCoreOf 2 M := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact h m hm a ha
    · rintro _ ⟨r, hr, rfl⟩
      exact Subgroup.mem_sup_right (uc22p22qh_conj_mem_pCoreOf hm hr)
  exact CFSG.Goldschmidt.G310.mem_normalizer_of_map_le hmap

theorem uc22p22qx_4a {p : ℕ} [Fact p.Prime] {M P₀ L P₁ : Subgroup G} (hP₀M : P₀ ≤ M) (hP₀ : IsPGroup p P₀)
    (hYn : M ≤ normalizer ((P₀ ⊔ uniqueFourPrimeCore p M : Subgroup G) : Set G))
    (hDM : centralizer (L : Set G) ≤ M)
    (hQ : ∀ q ∈ uniqueFourPrimeCore p M, ∃ r ∈ pCoreOf 2 M, ∃ d ∈ centralizer (L : Set G), q = r * d)
    (hP₀D : P₀ ≤ centralizer (L : Set G)) (hP₁L : P₁ ≤ L) (hP₁M : P₁ ≤ M)
    (hLR : ∀ y ∈ L, y ∈ pCoreOf 2 M → y = 1)
    (hLn : ∀ n ∈ normalizer (P₀ : Set G), ∀ x ∈ L, n * x * n⁻¹ ∈ L)
    (hfin : ∀ n ∈ normalizer (L : Set G), (∀ y ∈ P₁, n * y * n⁻¹ = y) →
      ∃ d ∈ centralizer (L : Set G), ∃ a ∈ P₁, n = d * a) :
    ∀ m ∈ M, (∀ x ∈ P₁, m * x * m⁻¹ * x⁻¹ ∈ pCoreOf 2 M) →
      m ∈ centralizer (L : Set G) ⊔ P₁ ⊔ pCoreOf 2 M := by
  intro m hm hcomm
  have hS : IsSylowOf p P₀ (P₀ ⊔ uniqueFourPrimeCore p M) := uc22p22qu_isSylowOf_sup hP₀M hP₀
  obtain ⟨y, hy, hn⟩ := uc22p22qq_frattini hS
    (fun m hm y hy => (mem_normalizer_iff.1 (hYn hm) y).1 hy) m hm
  have hP₀Q : P₀ ≤ normalizer (uniqueFourPrimeCore p M : Set G) := fun a ha =>
    uc22p22qk_mem_normalizer fun q hq => uc22p22qx_Q_conj (hP₀M ha) hq
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hP₀Q] at hy
  obtain ⟨q, hq, a₀, ha₀, rfl⟩ := hy
  obtain ⟨r, hr, d, hd, rfl⟩ := hQ q hq
  generalize hnd : (r * d * a₀)⁻¹ * m = n at hn
  have hRn : ∀ g ∈ M, ∀ w ∈ pCoreOf 2 M, g * w * g⁻¹ ∈ pCoreOf 2 M := fun g hg w hw =>
    uc22p22qh_conj_mem_pCoreOf hg hw
  have hDP : ∀ d ∈ centralizer (L : Set G), ∀ a ∈ P₁, d * a = a * d := fun d hd a ha =>
    (Subgroup.mem_centralizer_iff.1 hd a (hP₁L ha)).symm
  have hd' : d * a₀ ∈ centralizer (L : Set G) := (centralizer (L : Set G)).mul_mem hd (hP₀D ha₀)
  have hd'M : d * a₀ ∈ M := M.mul_mem (hDM hd) (hP₀M ha₀)
  have hrM : r ∈ M := (Subgroup.map_subtype_le _ : pCoreOf 2 M ≤ M) hr
  have hnM : n ∈ M := by
    rw [← hnd]
    exact M.mul_mem (M.inv_mem (M.mul_mem (M.mul_mem hrM (hDM hd)) (hP₀M ha₀))) hm
  have hnc : ∀ x ∈ P₁, n * x * n⁻¹ = x := by
    intro x hx
    have hxL : x ∈ L := hP₁L hx
    have hxM : x ∈ M := hP₁M hx
    have hdx : (d * a₀) * x = x * (d * a₀) := hDP (d * a₀) hd' x hx
    have hdx' : (d * a₀) * x⁻¹ = x⁻¹ * (d * a₀) := by
      calc (d * a₀) * x⁻¹ = x⁻¹ * (x * (d * a₀)) * x⁻¹ := by group
        _ = x⁻¹ * ((d * a₀) * x) * x⁻¹ := by rw [hdx]
        _ = x⁻¹ * (d * a₀) := by group
    have key : n * x * n⁻¹ * x⁻¹ =
        (d * a₀)⁻¹ * (r⁻¹ * (m * x * m⁻¹ * x⁻¹) * (x * r * x⁻¹)) * (d * a₀) := by
      rw [← hnd]
      calc (r * d * a₀)⁻¹ * m * x * ((r * d * a₀)⁻¹ * m)⁻¹ * x⁻¹
          = (r * d * a₀)⁻¹ * m * x * m⁻¹ * (r * ((d * a₀) * x⁻¹)) := by group
        _ = (r * d * a₀)⁻¹ * m * x * m⁻¹ * (r * (x⁻¹ * (d * a₀))) := by rw [hdx']
        _ = _ := by group
    have hρ : r⁻¹ * (m * x * m⁻¹ * x⁻¹) * (x * r * x⁻¹) ∈ pCoreOf 2 M :=
      (pCoreOf 2 M).mul_mem ((pCoreOf 2 M).mul_mem ((pCoreOf 2 M).inv_mem hr) (hcomm x hx))
        (hRn x hxM r hr)
    have hzR : n * x * n⁻¹ * x⁻¹ ∈ pCoreOf 2 M := by
      rw [key]
      have := hRn _ (M.inv_mem hd'M) _ hρ
      rwa [inv_inv] at this
    have hzL : n * x * n⁻¹ * x⁻¹ ∈ L := L.mul_mem (hLn n hn x hxL) (L.inv_mem hxL)
    exact mul_inv_eq_one.1 (hLR _ hzL hzR)
  have hnL : n ∈ normalizer (L : Set G) := uc22p22qk_mem_normalizer fun x hx => hLn n hn x hx
  obtain ⟨d₂, hd₂, a, ha, hna⟩ := hfin n hnL hnc
  have hmu : m = ((d * a₀ * d₂) * a) * (((d * a₀ * d₂) * a)⁻¹ * r * ((d * a₀ * d₂) * a)) := by
    have h1 : m = (r * d * a₀) * n := by rw [← hnd]; group
    rw [h1, hna]
    group
  have hu : (d * a₀ * d₂) * a ∈ centralizer (L : Set G) ⊔ P₁ :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ((centralizer (L : Set G)).mul_mem hd' hd₂))
      (Subgroup.mem_sup_right ha)
  have huM : (d * a₀ * d₂) * a ∈ M := M.mul_mem (M.mul_mem hd'M (hDM hd₂)) (hP₁M ha)
  have hr' : ((d * a₀ * d₂) * a)⁻¹ * r * ((d * a₀ * d₂) * a) ∈ pCoreOf 2 M := by
    have := hRn _ (M.inv_mem huM) r hr
    rwa [inv_inv] at this
  rw [hmu]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hr')

theorem uc22p22qx_orderOf {p : ℕ} [Fact p.Prime] {S : Subgroup G} (hS : IsPGroup p S) {a : G} (ha : a ∈ S) :
    ∃ k : ℕ, orderOf a = p ^ k := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hS ⟨a, ha⟩
  exact ⟨k, by rw [← hk]; exact (Subgroup.orderOf_mk a ha).symm⟩

theorem uc22p22qx_pow_mul {M : Subgroup G} {u r : G} (hu : u ∈ M) (hr : r ∈ pCoreOf 2 M) :
    ∀ k : ℕ, ∃ r' ∈ pCoreOf 2 M, (u * r) ^ k = u ^ k * r' := by
  intro k
  induction k with
  | zero => exact ⟨1, (pCoreOf 2 M).one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨r', hr', h⟩ := ih
    refine ⟨u⁻¹ * r' * u * r, (pCoreOf 2 M).mul_mem ?_ hr, ?_⟩
    · have := uc22p22qh_conj_mem_pCoreOf (M.inv_mem hu) hr'
      rwa [inv_inv] at this
    · rw [pow_succ, h, pow_succ]
      group

theorem uc22p22qx_4c {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {M T Dd P₁ : Subgroup G} (hT : IsPGroup 2 T)
    (hP₁M : P₁ ≤ M) (hDM : Dd ≤ M) (hP₁ : IsPGroup p P₁) (hDodd : ∀ d ∈ Dd, Odd (orderOf d))
    (hDP : ∀ d ∈ Dd, ∀ a ∈ P₁, d * a = a * d) :
    ∀ t ∈ T, t ∈ Dd ⊔ P₁ ⊔ pCoreOf 2 M → t ∈ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro t htT htD
  have hDn : Dd ≤ normalizer (pCoreOf 2 M : Set G) := fun d hd => uc22p22qu_M_le_normalizer_R M (hDM hd)
  have hPn : P₁ ≤ normalizer (pCoreOf 2 M : Set G) := fun a ha =>
    uc22p22qu_M_le_normalizer_R M (hP₁M ha)
  have hDPn : Dd ≤ normalizer (P₁ : Set G) := fun d hd =>
    uc22p22qk_mem_normalizer fun a ha => by
      have : d * a * d⁻¹ = a := by rw [hDP d hd a ha]; group
      rw [this]
      exact ha
  obtain ⟨d, hd, a, ha, r, hr, htdar⟩ := uc22p22ql_decomp hDn hPn hDPn hDP htD
  have hcomm : Commute d a := hDP d hd a ha
  have hodd : Odd (orderOf (d * a)) := by
    obtain ⟨k, hk⟩ := uc22p22qx_orderOf hP₁ ha
    have hao : Odd (orderOf a) := by
      rw [hk]
      exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    exact ((hDodd d hd).mul hao).of_dvd_nat hcomm.orderOf_mul_dvd_mul_orderOf
  have huM : d * a ∈ M := M.mul_mem (hDM hd) (hP₁M ha)
  obtain ⟨r', hr', hpow⟩ := uc22p22qx_pow_mul huM hr (orderOf (d * a))
  have htN : t ^ orderOf (d * a) ∈ pCoreOf 2 M := by
    rw [htdar, hpow, pow_orderOf_eq_one, one_mul]
    exact hr'
  obtain ⟨j, hj⟩ := uc22p22qx_orderOf hT htT
  have hcop : Nat.Coprime (orderOf t) (orderOf (d * a)) := by
    rw [hj]
    exact Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hodd)
  have hord : orderOf (t ^ orderOf (d * a)) = orderOf t := hcop.orderOf_pow
  have hle : Subgroup.zpowers (t ^ orderOf (d * a)) ≤ Subgroup.zpowers t := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers t) _
  have heq : Subgroup.zpowers (t ^ orderOf (d * a)) = Subgroup.zpowers t :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
  have hmem : t ∈ Subgroup.zpowers (t ^ orderOf (d * a)) := by
    rw [heq]
    exact Subgroup.mem_zpowers t
  exact (Subgroup.zpowers_le.2 htN) hmem

theorem uc22p22qx_autAt (D : Data G) (hstd : Sigma23Std D) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) (hd : UC6.R613DefAt D p P P₀) : UC6.R613AutAt D p P P₀ := by
  obtain ⟨⟨hp3, hsolv, hwc, hΓ, hL, hfrob⟩, hcent⟩ := id hd
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  haveI : Fact p.Prime := ⟨hpP⟩
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hP₀1 : P₀ ≠ ⊥ := by
    intro h
    have := hH.card
    rw [h, Subgroup.card_bot] at this
    exact hpP.one_lt.ne this
  have hSyl : IsSylowOf p (P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))) (UC6.inftyOf (centralizer (P₀ : Set G))) :=
    uc22p22q_isSylowOf_P1 D hstd hH hwc
  have hS' : IsSylowOf p ((P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))).subgroupOf
      (UC6.inftyOf (centralizer (P₀ : Set G)))) ⊤ := by
    have := (isSylowOf_map_subtype_iff (p := p) (UC6.inftyOf (centralizer (P₀ : Set G)))
      (A := (P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))).subgroupOf (UC6.inftyOf (centralizer (P₀ : Set G))))
      (B := ⊤)).1
    refine this ?_
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right, Subgroup.map_top, Subgroup.range_subtype]
    exact hSyl
  obtain ⟨n, -, hmodel⟩ := hL
  have hDM := (uc22p22qk_frob_unpack D hfrob).1
  have hLX : UC6.inftyOf (centralizer (P₀ : Set G)) ≤ centralizer (P₀ : Set G) := Subgroup.map_subtype_le _
  have hP₀D : P₀ ≤ centralizer ((UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.2 fun l hl => (Subgroup.mem_centralizer_iff.1 (hLX hl) z hz).symm
  have hP₁M : P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) ≤ D.M := inf_le_left.trans hH.sylow.le
  have hP₁p : IsPGroup p (P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) :=
    hH.sylow.isPGroup.to_inf_left
  have hQ := uc22p22qu_Q_le D hfrob
  have hDP : ∀ d ∈ centralizer ((UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G),
      ∀ a ∈ P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)), d * a = a * d := fun d hd a ha =>
    (Subgroup.mem_centralizer_iff.1 hd a ha.2).symm
  have hYP₁ := uc22p22qu_P1Q_normal D hstd hH hd
  have hconj := uc22p22qx_conj_le hP₁M hP₁p hYP₁ hQ hDP
  have h4a := uc22p22qx_4a (p := p) (hH.le.trans hH.sylow.le) (hH.sylow.isPGroup.to_le hH.le)
    (uc22p22qu_P0Q_normal D hH hsolv hwc) hDM hQ hP₀D inf_le_right hP₁M
    (uc22p22qu_L_inf_R D hP₀1 hLX hfrob)
    (fun n hn x hx => uc22p22q_inftyOf_conj (uc22p22q_mem_normalizer_centralizer hn) hx)
    (fun x hx hc => uc22p22qq_normalizer_centralizer_le hpP hp2 hmodel inf_le_right hS' hx hc)
  exact ⟨h4a, uc22p22qx_normalizes hconj, fun t ht hc =>
    uc22p22qx_4c hp2 D.sylowM.isPGroup hP₁M hDM hP₁p (uc22p22qu_Dd_odd D hfrob) hDP t ht
      (h4a t (D.sylowM.le ht) hc)⟩

theorem uc22p22q_r613aut_of (D : Data G) (hstd : Sigma23Std D) (h61 : UC6.R6_1 D) (hsp : Sigma2Print D)
    (hcent : UC6.R613Cent D) : UC6.R613Aut D :=
  (UC6.r613Aut_iff D).2 fun p P P₀ hH =>
    uc22p22qx_autAt D hstd hH
      (uc22p22q_r613defAt_all D hstd h61 hsp (uc22p22q_r613ident_of D hstd h61 hsp) hcent p P P₀ hH)

end CFSG.LocalAnalysis.UniquenessCase.UC22
