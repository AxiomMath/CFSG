module

public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A15Dihedral
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.VolI.A131

open scoped Pointwise MatrixGroups

@[expose] def A131Concl (p : ℕ) (Q : Type) [Group Q] : Prop :=
  (∀ S : Subgroup Q, IsPGroup 2 S → S ≠ ⊥ →
      IsCyclic ↥(CFSG.pCore p Q ⊓ Subgroup.centralizer (S : Set Q))) ∧
    CFSG.pRank 2 Q ≤ 2 ∧
    (CFSG.IsElementaryAbelian p ↥(CFSG.pCore p Q) → Nat.card ↥(CFSG.pCore p Q) = p ^ 3 →
      1 < CFSG.pRank 2 Q → ∃ K : Subgroup Q, K.Normal ∧ ⊥ < K ∧ K < CFSG.pCore p Q)

section Basic

variable {G : Type*} [Group G] [Finite G]

theorem odd_card_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G}
    (hK : IsPGroup p K) : Odd (Nat.card K) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).mp hK
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

omit [Finite G] in
theorem orderOf_ne_two_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G}
    (hK : IsPGroup p K) {x : G} (hx : x ∈ K) : orderOf x ≠ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hK) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  intro h2
  rw [h2] at hk
  rcases k with _ | k
  · simp at hk
  · have : p ∣ 2 := ⟨p ^ k, by rw [hk, pow_succ, mul_comm]⟩
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)

omit [Finite G] in
theorem orderOf_eq_of_prime {p : ℕ} (hp : p.Prime) {K : Subgroup G} (hK : IsPGroup p K) {x : G}
    (hx : x ∈ K) (hxp : (orderOf x).Prime) : orderOf x = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hK) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  exact ((Nat.Prime.pow_eq_iff hxp).mp hk.symm).1.symm

theorem exists_pow_involution (H : Subgroup G) [H.Normal] (hH : Odd (Nat.card H)) {g : G}
    (hg : orderOf (g : G ⧸ H) = 2) : ∃ m : ℕ, orderOf (g ^ m) = 2 ∧ ((g ^ m : G) : G ⧸ H) = g := by
  have hg2 : g ^ 2 ∈ H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hg, pow_orderOf_eq_one]
  have hodd : Odd (orderOf (g ^ 2)) := Odd.of_dvd_nat hH (Subgroup.orderOf_dvd_natCard H hg2)
  have hdvd : 2 ∣ orderOf g := by
    rw [← hg]
    exact orderOf_map_dvd (QuotientGroup.mk' H) g
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (orderOf_pos g).ne' (by rw [hm])
  have hm2 : orderOf (g ^ 2) = m := by
    rw [orderOf_pow_of_dvd two_ne_zero ⟨m, hm⟩, hm, Nat.mul_div_cancel_left m two_pos]
  rw [hm2] at hodd
  refine ⟨m, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd hm0 ⟨2, by rw [hm, mul_comm]⟩, hm, Nat.mul_div_cancel _ (by omega)]
  · rw [QuotientGroup.mk_pow, ← pow_mod_orderOf, hg, Nat.odd_iff.mp hodd, pow_one]

theorem exists_involution_lift (H : Subgroup G) [H.Normal] (hH : Odd (Nat.card H))
    {tb : G ⧸ H} (htb : orderOf tb = 2) : ∃ t : G, orderOf t = 2 ∧ (t : G ⧸ H) = tb := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective tb
  obtain ⟨m, hm, hmg⟩ := exists_pow_involution H hH htb
  exact ⟨g ^ m, hm, hmg⟩

theorem exists_centralizer_lift (H : Subgroup G) [hHn : H.Normal] (hH : Odd (Nat.card H)) {t : G}
    (ht : orderOf t = 2) {xb : G ⧸ H} (hxb : xb * (t : G ⧸ H) = (t : G ⧸ H) * xb) :
    ∃ x : G, x * t = t * x ∧ (x : G ⧸ H) = xb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have : Fact (IsPGroup 2 (Subgroup.zpowers t)) := ⟨h2⟩
  have key : Subgroup.centralizer
      (((Subgroup.zpowers t).map (QuotientGroup.mk' H) : Subgroup (G ⧸ H)) : Set (G ⧸ H)) =
      (Subgroup.centralizer (Subgroup.zpowers t : Set G)).map (QuotientGroup.mk' H) :=
    CFSG.centralizer_map_quotient_eq_map_centralizer 2 (Subgroup.zpowers t) H hHn
      (Nat.coprime_two_left.mpr hH)
  have hmem : xb ∈ Subgroup.centralizer
      (((Subgroup.zpowers t).map (QuotientGroup.mk' H) : Subgroup (G ⧸ H)) : Set (G ⧸ H)) := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    exact hxb
  rw [key] at hmem
  obtain ⟨x, hx, rfl⟩ := hmem
  have hx' : x ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
    exact hx
  exact ⟨x, Subgroup.mem_centralizer_singleton_iff.mp hx', rfl⟩

omit [Finite G] in
theorem isElemAbelian_map_subtype {p : ℕ} {K : Subgroup G} {S : Subgroup K}
    [hS : CFSG.IsElementaryAbelian p ↥S] : CFSG.Open.IsElemAbelian p (S.map K.subtype) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
    obtain ⟨_, ⟨b, hb, rfl⟩⟩ := y
    apply Subtype.ext
    show ((a : K) : G) * b = b * a
    have := congrArg (fun z : ↥S => ((z : K) : G))
      (hS.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    simpa using this
  · rintro _ ⟨a, ha, rfl⟩
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := S) a ha
    simpa using congrArg Subtype.val this

end Basic

section One

variable {G : Type*} [Group G] [Finite G]

theorem isCyclic_inf_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : CFSG.pRank p G ≤ 2) (H : Subgroup G) [H.Normal] (hH : IsPGroup p H)
    (hC : Subgroup.centralizer (CFSG.pCore p (G ⧸ H) : Set (G ⧸ H)) ≤ CFSG.pCore p (G ⧸ H))
    {tb : G ⧸ H} (htb : orderOf tb = 2) :
    IsCyclic ↥(CFSG.pCore p (G ⧸ H) ⊓ Subgroup.centralizer ({tb} : Set (G ⧸ H))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set π : G →* G ⧸ H := QuotientGroup.mk' H with hπ
  set Pb := CFSG.pCore p (G ⧸ H) with hPbdef
  set P := Pb.comap π with hPdef
  have hPb2 : IsPGroup p Pb := CFSG.pCore_isPGroup
  have hP : IsPGroup p P :=
    hPb2.comap_of_ker_isPGroup π (by rw [hπ, QuotientGroup.ker_mk']; exact hH)
  have hPbn : Pb.Normal := CFSG.pCore_normal
  have hPn : P.Normal := hPbn.comap π
  have hHodd : Odd (Nat.card H) := odd_card_of_isPGroup hp hp2 hH
  obtain ⟨t, ht, htb'⟩ := exists_involution_lift H hHodd htb
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  set C := P ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
  have hCmap : Pb ⊓ Subgroup.centralizer ({tb} : Set (G ⧸ H)) ≤ C.map π := by
    rintro xb ⟨hxP, hxc⟩
    have hxc' := Subgroup.mem_centralizer_singleton_iff.mp hxc
    obtain ⟨x, hxt, rfl⟩ := exists_centralizer_lift H hHodd ht (xb := xb) (by
      rw [htb']
      exact hxc')
    exact ⟨x, ⟨hxP, Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩, rfl⟩
  by_contra hnc
  have hCnc : ¬ IsCyclic ↥C := by
    intro hcyc
    apply hnc
    have : IsCyclic ↥(C.map π) := isCyclic_of_surjective _ (π.subgroupMap_surjective C)
    exact Subgroup.isCyclic_of_le hCmap
  have hCp : IsPGroup p C := hP.to_le inf_le_left
  have : Fact (IsPGroup p ↥C) := ⟨hCp⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hCnc
  set E := S.map C.subtype with hEdef
  have hEC : E ≤ C := Subgroup.map_subtype_le S
  have hEcard : Nat.card E = p ^ 2 := by
    rw [hEdef, Subgroup.card_map_of_injective C.subtype_injective, hScard]
  have hEel : CFSG.Open.IsElemAbelian p E := isElemAbelian_map_subtype
  have htP : ¬ ∀ x ∈ P, t * x = x * t := by
    intro h
    have htbC : tb ∈ Subgroup.centralizer (Pb : Set (G ⧸ H)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro yb hyb
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
      have hy : y ∈ P := hyb
      rw [← htb', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h y hy]
    exact orderOf_ne_two_of_isPGroup hp hp2 hPb2 (hC htbC) htb
  let ρ : G →* MulAut ↥P := MulAut.conjNormal
  have hρ : ∀ (g : G) (x : ↥P), ((ρ g x : ↥P) : G) = g * x * g⁻¹ := fun g x =>
    MulAut.conjNormal_apply g x
  have hB : IsPGroup p ↥(C.map ρ) := hCp.map ρ
  have ha : (orderOf t).Coprime p := by
    rw [ht]
    exact Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)
  have hcomm : ∀ b ∈ C, ρ t * ρ b = ρ b * ρ t := fun b hb => by
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_singleton_iff.mp hb.2)]
  obtain ⟨x, hxfix, hxt⟩ : ∃ x : ↥P, (∀ b ∈ C, ρ b x = x) ∧ ρ t x ≠ x := by
    by_contra hall
    push Not at hall
    have h1 := CFSG.Quasithin.thompson_AxB_element (p := p) hP ρ hB ha hcomm hall
    apply htP
    intro y hy
    have h2 := congrArg (fun φ : MulAut ↥P => ((φ ⟨y, hy⟩ : ↥P) : G)) h1
    simp only [MulAut.one_apply, hρ] at h2
    calc t * y = t * y * t⁻¹ * t := by group
      _ = y * t := by rw [h2]
  set Z := P ⊓ Subgroup.centralizer (C : Set G) with hZdef
  have hZodd : Odd (Nat.card Z) := odd_card_of_isPGroup hp hp2 (hP.to_le inf_le_left)
  have htC : ∀ c ∈ C, t * c * t⁻¹ = c := fun c hc => by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp hc.2).symm, mul_inv_cancel_right]
  have hZt : ∀ z ∈ Z, t * z * t⁻¹ ∈ Z := by
    intro z hz
    refine ⟨hPn.conj_mem z hz.1 t, Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩
    have hzc := Subgroup.mem_centralizer_iff.mp hz.2 c hc
    have hc' := htC c hc
    calc c * (t * z * t⁻¹) = (t * c * t⁻¹) * (t * z * t⁻¹) := by rw [hc']
      _ = t * (c * z) * t⁻¹ := by group
      _ = t * (z * c) * t⁻¹ := by rw [hzc]
      _ = (t * z * t⁻¹) * (t * c * t⁻¹) := by group
      _ = (t * z * t⁻¹) * c := by rw [hc']
  have hxZ : (x : G) ∈ Z := by
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩
    have h1 := congrArg Subtype.val (hxfix c hc)
    rw [hρ] at h1
    calc c * x = c * x * c⁻¹ * c := by group
      _ = x * c := by rw [h1]
  have hxt' : t * (x : G) * t⁻¹ ≠ x := fun h => hxt (Subtype.ext (by rw [hρ]; exact h))
  obtain ⟨y, hyZ, hyord, hyinv⟩ := CFSG.Quasithin.G8.exists_inverted_prime ht2 hZodd hZt
    ⟨x, hxZ, hxt'⟩
  have hyp : orderOf y = p := orderOf_eq_of_prime hp hP hyZ.1 hyord
  have hyE : y ∉ E := by
    intro hy
    have h1 := htC y (hEC hy)
    rw [hyinv] at h1
    have h2 : y ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← h1]
      exact inv_mul_cancel y
    have h3 : p ∣ 2 := hyp ▸ orderOf_dvd_of_pow_eq_one h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  have hEy : ∀ e ∈ E, Commute e y := fun e he =>
    (Subgroup.mem_centralizer_iff.mp hyZ.2 e (hEC he))
  obtain ⟨hF, hFcard⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hEel hyp hEy hyE
  have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) :=
    CFSG.Quasithin.le_pRank hp le_top hF (by rw [hFcard, hEcard]; ring)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hr
  omega

theorem isCyclic_of_involutions {Q : Type*} [Group Q] [Finite Q] {Pb : Subgroup Q}
    (hinv : ∀ tb : Q, orderOf tb = 2 → IsCyclic ↥(Pb ⊓ Subgroup.centralizer ({tb} : Set Q)))
    (S : Subgroup Q) (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) :
    IsCyclic ↥(Pb ⊓ Subgroup.centralizer (S : Set Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hS
  have h2 : 2 ∣ Nat.card S := by
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact absurd hk (Finite.one_lt_card).ne'
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨tb, htb⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hcyc := hinv tb (by rwa [Subgroup.orderOf_coe])
  refine Subgroup.isCyclic_of_le (H' := Pb ⊓ Subgroup.centralizer ({(tb : Q)} : Set Q)) ?_
  exact inf_le_inf_left _ (Subgroup.centralizer_le (by simp))

end One

section Two

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem mem_of_mem_sup_of_odd {Pb A : Subgroup Q} [hPbn : Pb.Normal] (hA : ∀ a ∈ A, a ^ 2 = 1)
    {x : Q} (hx : x ∈ Pb ⊔ A) (hodd : Odd (orderOf x)) : x ∈ Pb := by
  have hx' : x ∈ (Pb : Set Q) * (A : Set Q) := by
    rw [← Subgroup.normal_mul]
    exact hx
  obtain ⟨y, hy, a, ha, rfl⟩ := Set.mem_mul.mp hx'
  have hsq : (y * a) ^ 2 ∈ Pb := by
    have ha2 : a * a = 1 := by rw [← pow_two]; exact hA a ha
    have e : (y * a) ^ 2 = y * (a * y * a⁻¹) * (a * a) := by rw [pow_two]; group
    rw [e, ha2, mul_one]
    exact Pb.mul_mem hy (hPbn.conj_mem y hy a)
  have hcop : Nat.Coprime 2 (orderOf (y * a)) := Nat.coprime_two_left.mpr hodd
  exact (Subgroup.zpowers_le.mpr hsq) (CFSG.Quasithin.A4.mem_zpowers_pow_of_coprime hcop)

omit [Finite Q] in
theorem isElemAbelian_zpowers {p : ℕ} {x : Q} (hx : x ^ p = 1) :
    CFSG.Open.IsElemAbelian p (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

omit [Finite Q] in
theorem card_le_of_isCyclic {p : ℕ} (hp : 0 < p) {C : Subgroup Q} [IsCyclic ↥C]
    (hC : ∀ x ∈ C, x ^ p = 1) : Nat.card C ≤ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥C)
  have h1 : orderOf g ∣ p := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (by simpa using hC g g.2)
  rw [hg] at h1
  exact Nat.le_of_dvd hp h1

theorem pRank_two_le_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hC : Subgroup.centralizer (CFSG.pCore p Q : Set Q) ≤ CFSG.pCore p Q)
    (hinv : ∀ tb : Q, orderOf tb = 2 →
      IsCyclic ↥(CFSG.pCore p Q ⊓ Subgroup.centralizer ({tb} : Set Q))) :
    CFSG.pRank 2 Q ≤ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Pb := CFSG.pCore p Q with hPbdef
  have hPb2 : IsPGroup p Pb := CFSG.pCore_isPGroup
  have hPbn : Pb.Normal := CFSG.pCore_normal
  by_contra hlt
  push Not at hlt
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hlt
  obtain ⟨A, -, hA, hAcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (k := 3) (by omega)
      (H := (⊤ : Subgroup Q)) (p := 2)
  have hPbodd : Odd (Nat.card Pb) := odd_card_of_isPGroup hp hp2 hPb2
  have hAN : A ≤ Subgroup.normalizer (Pb : Set Q) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hfaith : A ⊓ Subgroup.centralizer (Pb : Set Q) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzP : z ∈ Pb := hC hz.2
    rw [Subgroup.mem_bot]
    by_contra hz1
    exact orderOf_ne_two_of_isPGroup hp hp2 hPb2 hzP (orderOf_eq_prime (hA.2 z hz.1) hz1)
  obtain ⟨Hs, ps, hD, -, hHle⟩ := CFSG.Quasithin.a1_5 hPbodd hA hAN hfaith hAcard
  obtain ⟨e0⟩ := hD.iso 0
  obtain ⟨e1⟩ := hD.iso 1
  obtain ⟨e2⟩ := hD.iso 2
  set t : Q := ((e0.symm (DihedralGroup.sr 0) : ↥(Hs 0)) : Q) with htdef
  set r1 : Q := ((e1.symm (DihedralGroup.r 1) : ↥(Hs 1)) : Q) with hr1def
  set r2 : Q := ((e2.symm (DihedralGroup.r 1) : ↥(Hs 2)) : Q) with hr2def
  have ht : orderOf t = 2 := by
    rw [htdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  have hr1o : orderOf r1 = ps 1 := by
    rw [hr1def, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hr2o : orderOf r2 = ps 2 := by
    rw [hr2def, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have htH : t ∈ Hs 0 := (e0.symm _).2
  have hr1H : r1 ∈ Hs 1 := (e1.symm _).2
  have hr2H : r2 ∈ Hs 2 := (e2.symm _).2
  have hr1P : r1 ∈ Pb := mem_of_mem_sup_of_odd hA.2 (hHle (Subgroup.mem_iSup_of_mem 1 hr1H))
    (by rw [hr1o]; exact hD.odd 1)
  have hr2P : r2 ∈ Pb := mem_of_mem_sup_of_odd hA.2 (hHle (Subgroup.mem_iSup_of_mem 2 hr2H))
    (by rw [hr2o]; exact hD.odd 2)
  have hp1 : orderOf r1 = p := orderOf_eq_of_prime hp hPb2 hr1P (by rw [hr1o]; exact hD.prime 1)
  have hp2' : orderOf r2 = p :=
    orderOf_eq_of_prime hp hPb2 hr2P (by rw [hr2o]; exact hD.prime 2)
  have hc01 : t * r1 = r1 * t := hD.commute 0 1 (by decide) t htH r1 hr1H
  have hc02 : t * r2 = r2 * t := hD.commute 0 2 (by decide) t htH r2 hr2H
  have hc12 : r1 * r2 = r2 * r1 := hD.commute 1 2 (by decide) r1 hr1H r2 hr2H
  have hdisj : Disjoint (Hs 1) (Hs 2) :=
    hD.independent.pairwiseDisjoint (by decide : (1 : Fin 3) ≠ 2)
  have hE1 : CFSG.Open.IsElemAbelian p (Subgroup.zpowers r1) :=
    isElemAbelian_zpowers (by rw [← hp1]; exact pow_orderOf_eq_one r1)
  have hr2E : r2 ∉ Subgroup.zpowers r1 := by
    intro h
    have h1 : r2 ∈ Hs 1 := (Subgroup.zpowers_le.mpr hr1H) h
    have h2 : r2 = 1 := Subgroup.mem_bot.mp (hdisj.le_bot ⟨h1, hr2H⟩)
    rw [h2, orderOf_one] at hp2'
    exact hp.one_lt.ne hp2'
  have hcomm2 : ∀ e ∈ Subgroup.zpowers r1, Commute e r2 := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact Commute.zpow_left hc12 k
  obtain ⟨hEel, hEcard⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE1 hp2' hcomm2 hr2E
  have hEle : Subgroup.zpowers r1 ⊔ Subgroup.zpowers r2 ≤
      Pb ⊓ Subgroup.centralizer ({t} : Set Q) := by
    refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le]
    · exact ⟨hr1P, Subgroup.mem_centralizer_singleton_iff.mpr hc01.symm⟩
    · exact ⟨hr2P, Subgroup.mem_centralizer_singleton_iff.mpr hc02.symm⟩
  have hcyc := hinv t ht
  have hEcyc : IsCyclic ↥(Subgroup.zpowers r1 ⊔ Subgroup.zpowers r2) :=
    Subgroup.isCyclic_of_le hEle
  have hle := card_le_of_isCyclic hp.pos hEel.2
  rw [hEcard, Nat.card_zpowers, hp1] at hle
  nlinarith [hp.two_le]

end Two

section GLTwo

variable {F : Type*} [Field F]

theorem det_eq_neg_one {x : GL (Fin 2) F} (hx : x * x = 1) (hx1 : x ≠ 1) (hxm : x ≠ -1) :
    (x : Matrix (Fin 2) (Fin 2) F).det = -1 := by
  set M : Matrix (Fin 2) (Fin 2) F := x.val with hM
  have hMM : M * M = 1 := by
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) hx
    simpa [hM] using this
  have h00 := congrFun (congrFun hMM 0) 0
  have h01 := congrFun (congrFun hMM 0) 1
  have h10 := congrFun (congrFun hMM 1) 0
  have h11 := congrFun (congrFun hMM 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h00 h01 h10 h11
  rw [Matrix.det_fin_two]
  by_cases htr : M 0 0 + M 1 1 = 0
  · have hd : M 1 1 = - M 0 0 := by linear_combination htr
    rw [hd]
    linear_combination -h00
  · exfalso
    have hb : M 0 1 = 0 := by
      have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination h01
      exact (mul_eq_zero.mp this).resolve_right htr
    have hc : M 1 0 = 0 := by
      have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination h10
      exact (mul_eq_zero.mp this).resolve_right htr
    have ha2 : M 0 0 * M 0 0 = 1 := by rw [hb] at h00; linear_combination h00
    have hd2 : M 1 1 * M 1 1 = 1 := by rw [hc] at h11; linear_combination h11
    have had : M 0 0 = M 1 1 := by
      have : (M 0 0 - M 1 1) * (M 0 0 + M 1 1) = 0 := by linear_combination ha2 - hd2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right htr)
    have hMeq : ∀ c : F, M 0 0 = c → M = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
      intro c hc'
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, ← had, hc']
    rcases mul_self_eq_one_iff.mp ha2 with h1 | h1
    · apply hx1
      apply Units.ext
      rw [← hM, hMeq 1 h1, one_smul, Units.val_one]
    · apply hxm
      apply Units.ext
      rw [← hM, hMeq (-1) h1, neg_one_smul, Units.val_neg, Units.val_one]

theorem neg_one_of_commuting {x y : GL (Fin 2) F} (hF : (2 : F) ≠ 0) (hx : x * x = 1)
    (hy : y * y = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy1 : x * y ≠ 1) :
    x = -1 ∨ y = -1 ∨ x * y = -1 := by
  by_contra h
  push Not at h
  obtain ⟨hxm, hym, hxym⟩ := h
  have hdx := det_eq_neg_one hx hx1 hxm
  have hdy := det_eq_neg_one hy hy1 hym
  have hxy2 : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx, hy, mul_one]
  have hdxy := det_eq_neg_one hxy2 hxy1 hxym
  rw [Units.val_mul, Matrix.det_mul, hdx, hdy] at hdxy
  exact hF (by linear_combination hdxy)

end GLTwo

section Three

variable {G : Type*} [Group G] [Finite G]

theorem exists_central_mod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : CFSG.pRank p G ≤ 2)
    (H : Subgroup G) [H.Normal] (hH : IsPGroup p H)
    (hC : Subgroup.centralizer (CFSG.pCore p (G ⧸ H) : Set (G ⧸ H)) ≤ CFSG.pCore p (G ⧸ H))
    {ab bb : G ⧸ H} (hab : orderOf ab = 2) (hbb : orderOf bb = 2) (hcab : ab * bb = bb * ab)
    (hne : ab ≠ bb) :
    ∃ tb : G ⧸ H, (tb = ab ∨ tb = bb ∨ tb = ab * bb) ∧
      ∀ gb : G ⧸ H, gb * tb * gb⁻¹ * tb⁻¹ ∈ CFSG.pCore p (G ⧸ H) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set π : G →* G ⧸ H := QuotientGroup.mk' H with hπ
  set Pb := CFSG.pCore p (G ⧸ H) with hPbdef
  set P := Pb.comap π with hPdef
  have hPb2 : IsPGroup p Pb := CFSG.pCore_isPGroup
  have hP : IsPGroup p P :=
    hPb2.comap_of_ker_isPGroup π (by rw [hπ, QuotientGroup.ker_mk']; exact hH)
  have hPbn : Pb.Normal := CFSG.pCore_normal
  have hPn : P.Normal := hPbn.comap π
  have hHodd : Odd (Nat.card H) := odd_card_of_isPGroup hp hp2 hH
  have hCP : ∀ g : G, (∀ x ∈ P, x * g = g * x) → g ∈ P := by
    intro g hg
    show π g ∈ Pb
    apply hC
    rw [Subgroup.mem_centralizer_iff]
    intro yb hyb
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
    have hy : y ∈ P := hyb
    rw [hπ, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hg y hy]
  have hrP : CFSG.Open.pRank p (⊤ : Subgroup ↥P) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp]
    calc CFSG.Open.pRank p P ≤ CFSG.Open.pRank p (⊤ : Subgroup G) :=
          CFSG.SectionRank.pRank_mono hp.one_lt le_top
      _ = CFSG.pRank p G := (CFSG.SectionRank.pRank_eq_open_pRank_top p G).symm
      _ ≤ 2 := hr
  obtain ⟨φ, hφ⟩ := CFSG.Quasithin.exists_hom_ker_eq_pCore_aut (P := ↥P) hp2 hP hrP
  set ψ : G →* GL (Fin 2) (ZMod p) := φ.comp MulAut.conjNormal with hψdef
  have hkerP : ∀ g : G, ψ g = 1 → g ∈ P := by
    have hK2 : IsPGroup p ψ.ker := by
      intro g
      have hgφ : MulAut.conjNormal (g : G) ∈ φ.ker := g.2
      rw [hφ] at hgφ
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup p) ⟨_, hgφ⟩
      have hk' : MulAut.conjNormal ((g : G) ^ p ^ k) = (1 : MulAut ↥P) := by
        rw [map_pow]
        exact congrArg Subtype.val hk
      have hgk : (g : G) ^ p ^ k ∈ P := by
        refine hCP _ fun x hx => ?_
        have h1 := congrArg (fun φ : MulAut ↥P => ((φ ⟨x, hx⟩ : ↥P) : G)) hk'
        simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
        calc x * (g : G) ^ p ^ k = (g : G) ^ p ^ k * x * ((g : G) ^ p ^ k)⁻¹ *
              (g : G) ^ p ^ k := by rw [h1]
          _ = (g : G) ^ p ^ k * x := by group
      obtain ⟨j, hj⟩ := hP ⟨_, hgk⟩
      refine ⟨k + j, Subtype.ext ?_⟩
      have := congrArg Subtype.val hj
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
      rw [pow_add, pow_mul]
      exact this
    have hKn : ψ.ker.Normal := ψ.normal_ker
    have hmap : ψ.ker.map π ≤ Pb :=
      le_sSup ⟨hKn.map π (QuotientGroup.mk'_surjective H), hK2.map π⟩
    exact fun g hg => hmap ⟨g, hg, rfl⟩
  have hnotP : ∀ g : G, orderOf g = 2 → ψ g ≠ 1 := fun g hg h1 =>
    orderOf_ne_two_of_isPGroup hp hp2 hP (hkerP g h1) hg
  obtain ⟨a, ha, rfl⟩ := exists_involution_lift H hHodd hab
  obtain ⟨b₀, hb₀, rfl⟩ := exists_centralizer_lift H hHodd ha (xb := bb) hcab.symm
  obtain ⟨m, hbm, hbmb⟩ := exists_pow_involution H hHodd hbb
  set b := b₀ ^ m with hbdef
  have hab' : a * b = b * a := by rw [hbdef]; exact (Commute.pow_right hb₀.symm m).eq
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hb2 : b * b = 1 := by rw [← pow_two, ← hbm, pow_orderOf_eq_one]
  have hπab : (π (a * b) : G ⧸ H) = (a : G ⧸ H) * b₀ := by
    rw [map_mul]
    exact congrArg _ hbmb
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hne
    have := congrArg π h
    rw [hπab, map_one] at this
    have hbb2 : (b₀ : G ⧸ H) * b₀ = 1 := by rw [← pow_two, ← hbb, pow_orderOf_eq_one]
    calc (a : G ⧸ H) = (a : G ⧸ H) * (b₀ * b₀) := by rw [hbb2, mul_one]
      _ = (a * b₀) * b₀ := by group
      _ = b₀ := by rw [this, one_mul]
  have habo : orderOf (a * b) = 2 := by
    refine orderOf_eq_prime ?_ hab1
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
      _ = a * (a * b) * b := by rw [hab']
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  have hF2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hψa : ψ a * ψ a = 1 := by rw [← map_mul, ha2, map_one]
  have hψb : ψ b * ψ b = 1 := by rw [← map_mul, hb2, map_one]
  have hψab : ψ a * ψ b = ψ b * ψ a := by rw [← map_mul, ← map_mul, hab']
  have hψab1 : ψ a * ψ b ≠ 1 := by rw [← map_mul]; exact hnotP _ habo
  have hcen : ∀ s : G, ψ s = -1 → ∀ gb : G ⧸ H, gb * π s * gb⁻¹ * (π s)⁻¹ ∈ Pb := by
    intro s hs gb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    have h1 : ψ (g * s * g⁻¹ * s⁻¹) = 1 := by
      simp only [map_mul, map_inv, hs]
      rw [mul_neg_one, neg_mul, mul_inv_cancel, inv_neg_one, mul_neg_one, neg_neg]
    have := hkerP _ h1
    rw [hPdef, Subgroup.mem_comap] at this
    simpa [hπ] using this
  rcases neg_one_of_commuting hF2 hψa hψb hψab (hnotP a ha) (hnotP b hbm) hψab1 with
    h | h | h
  · exact ⟨π a, Or.inl rfl, hcen a h⟩
  · exact ⟨π b, Or.inr (Or.inl hbmb), hcen b h⟩
  · rw [← map_mul] at h
    exact ⟨π (a * b), Or.inr (Or.inr hπab), hcen (a * b) h⟩

end Three

section Irr

variable {Q : Type*} [Group Q] [Finite Q]

theorem false_of_irreducible {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hC : Subgroup.centralizer (CFSG.pCore p Q : Set Q) ≤ CFSG.pCore p Q)
    (hinv : ∀ tb : Q, orderOf tb = 2 →
      IsCyclic ↥(CFSG.pCore p Q ⊓ Subgroup.centralizer ({tb} : Set Q)))
    (hel : CFSG.IsElementaryAbelian p ↥(CFSG.pCore p Q))
    (hcard : Nat.card ↥(CFSG.pCore p Q) = p ^ 3)
    (hirr : ∀ K : Subgroup Q, K.Normal → ⊥ < K → K < CFSG.pCore p Q → False)
    {tb sb : Q} (htb : orderOf tb = 2) (hsb : orderOf sb = 2) (hts : tb * sb = sb * tb)
    (hne : tb ≠ sb) (hcent : ∀ gb : Q, gb * tb * gb⁻¹ * tb⁻¹ ∈ CFSG.pCore p Q) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Pb := CFSG.pCore p Q with hPbdef
  have hPb2 : IsPGroup p Pb := CFSG.pCore_isPGroup
  have hPbn : Pb.Normal := CFSG.pCore_normal
  have hab : ∀ x ∈ Pb, ∀ y ∈ Pb, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hel.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ Pb, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := Pb) x hx
  have htb2 : tb * tb = 1 := by rw [← pow_two, ← htb, pow_orderOf_eq_one]
  have hsb2 : sb * sb = 1 := by rw [← pow_two, ← hsb, pow_orderOf_eq_one]
  have htinv : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right htb2
  have hsinv : sb⁻¹ = sb := inv_eq_of_mul_eq_one_right hsb2
  set Ct := Pb ⊓ Subgroup.centralizer ({tb} : Set Q) with hCtdef
  have hCtn : Ct.Normal := by
    refine ⟨fun x hx g => ⟨hPbn.conj_mem x hx.1 g, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩⟩
    have hxt := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    set c := g⁻¹ * tb * g * tb⁻¹ with hc
    have hcP : c ∈ Pb := by simpa [hc] using hcent g⁻¹
    have hxc : x * c = c * x := hab x hx.1 c hcP
    have e : g⁻¹ * tb * g = c * tb := by rw [hc]; group
    have key : x * (g⁻¹ * tb * g) = (g⁻¹ * tb * g) * x := by
      rw [e, ← mul_assoc, hxc, mul_assoc, hxt, ← mul_assoc]
    calc g * x * g⁻¹ * tb = g * (x * (g⁻¹ * tb * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * tb * g) * x) * g⁻¹ := by rw [key]
      _ = tb * (g * x * g⁻¹) := by group
  have hCt : Ct = ⊥ := by
    by_contra h
    rcases (inf_le_left : Ct ≤ Pb).lt_or_eq with hlt | heq
    · exact hirr Ct hCtn (bot_lt_iff_ne_bot.mpr h) hlt
    · have htC : tb ∈ Subgroup.centralizer (Pb : Set Q) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : y ∈ Pb ⊓ Subgroup.centralizer ({tb} : Set Q) := by rw [heq]; exact hy
        exact Subgroup.mem_centralizer_singleton_iff.mp hy'.2
      exact orderOf_ne_two_of_isPGroup hp hp2 hPb2 (hC htC) htb
  have hinvt : ∀ v ∈ Pb, tb * v * tb⁻¹ = v⁻¹ := by
    intro v hv
    have hvt : tb * v * tb⁻¹ ∈ Pb := hPbn.conj_mem v hv tb
    have hw : v * (tb * v * tb⁻¹) ∈ Ct := by
      refine ⟨Pb.mul_mem hv hvt, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hc := hab v hv _ hvt
      rw [htinv] at hc ⊢
      calc v * (tb * v * tb) * tb = v * tb * v * (tb * tb) := by group
        _ = (tb * tb) * v * tb * v := by rw [htb2, mul_one, one_mul]
        _ = tb * ((tb * v * tb) * v) := by group
        _ = tb * (v * (tb * v * tb)) := by rw [← hc]
    rw [hCt, Subgroup.mem_bot] at hw
    exact eq_inv_of_mul_eq_one_right hw
  set C1 := Pb ⊓ Subgroup.centralizer ({sb} : Set Q) with hC1def
  set C2 := Pb ⊓ Subgroup.centralizer ({tb * sb} : Set Q) with hC2def
  have hts2 : orderOf (tb * sb) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · calc (tb * sb) ^ 2 = tb * (sb * tb) * sb := by rw [pow_two]; group
        _ = tb * (tb * sb) * sb := by rw [hts]
        _ = (tb * tb) * (sb * sb) := by group
        _ = 1 := by rw [htb2, hsb2, mul_one]
    · intro h
      apply hne
      calc tb = tb * (sb * sb) := by rw [hsb2, mul_one]
        _ = (tb * sb) * sb := by group
        _ = sb := by rw [h, one_mul]
  have hle : Pb ≤ C1 ⊔ C2 := by
    intro v hv
    have hsv : sb * v * sb⁻¹ ∈ Pb := hPbn.conj_mem v hv sb
    have hu : v * (sb * v * sb⁻¹) ∈ C1 := by
      refine ⟨Pb.mul_mem hv hsv, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hc := hab v hv _ hsv
      rw [hsinv] at hc ⊢
      calc v * (sb * v * sb) * sb = v * sb * v * (sb * sb) := by group
        _ = (sb * sb) * v * sb * v := by rw [hsb2, mul_one, one_mul]
        _ = sb * ((sb * v * sb) * v) := by group
        _ = sb * (v * (sb * v * sb)) := by rw [← hc]
    have hwP : v * (sb * v * sb⁻¹)⁻¹ ∈ Pb := Pb.mul_mem hv (Pb.inv_mem hsv)
    have hss : sb * sb * v * sb⁻¹ * sb⁻¹ = v := by
      rw [hsb2, one_mul, mul_assoc, ← mul_inv_rev, hsb2, inv_one, mul_one]
    have hsw : sb * (v * (sb * v * sb⁻¹)⁻¹) * sb⁻¹ = (v * (sb * v * sb⁻¹)⁻¹)⁻¹ := by
      calc sb * (v * (sb * v * sb⁻¹)⁻¹) * sb⁻¹ =
            (sb * v * sb⁻¹) * (sb * sb * v * sb⁻¹ * sb⁻¹)⁻¹ := by group
        _ = (sb * v * sb⁻¹) * v⁻¹ := by rw [hss]
        _ = (v * (sb * v * sb⁻¹)⁻¹)⁻¹ := by group
    have hw : v * (sb * v * sb⁻¹)⁻¹ ∈ C2 := by
      refine ⟨hwP, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      set w := v * (sb * v * sb⁻¹)⁻¹ with hwdef
      have hconj : (tb * sb) * w * (tb * sb)⁻¹ = w := by
        calc (tb * sb) * w * (tb * sb)⁻¹ = tb * (sb * w * sb⁻¹) * tb⁻¹ := by group
          _ = tb * w⁻¹ * tb⁻¹ := by rw [hsw]
          _ = (tb * w * tb⁻¹)⁻¹ := by group
          _ = w := by rw [hinvt w hwP, inv_inv]
      calc w * (tb * sb) = ((tb * sb) * w * (tb * sb)⁻¹) * (tb * sb) := by rw [hconj]
        _ = (tb * sb) * w := by group
    have hv2 : v ^ 2 = (v * (sb * v * sb⁻¹)) * (v * (sb * v * sb⁻¹)⁻¹) := by
      have hc := hab v hv _ hsv
      calc v ^ 2 = v * (v * (sb * v * sb⁻¹)) * (sb * v * sb⁻¹)⁻¹ := by rw [pow_two]; group
        _ = v * ((sb * v * sb⁻¹) * v) * (sb * v * sb⁻¹)⁻¹ := by rw [hc]
        _ = (v * (sb * v * sb⁻¹)) * (v * (sb * v * sb⁻¹)⁻¹) := by group
    have hk : v = (v ^ 2) ^ ((p + 1) / 2) := by
      rw [← pow_mul]
      have hodd := hp.odd_of_ne_two hp2
      have : 2 * ((p + 1) / 2) = p + 1 := by obtain ⟨k, hk⟩ := hodd; omega
      rw [this, pow_succ, hexp v hv, one_mul]
    rw [hk, hv2]
    exact Subgroup.pow_mem _
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hw)) _
  have hC1 : Nat.card C1 ≤ p := by
    have := hinv sb hsb
    exact card_le_of_isCyclic hp.pos fun x hx => hexp x hx.1
  have hC2 : Nat.card C2 ≤ p := by
    have := hinv (tb * sb) hts2
    exact card_le_of_isCyclic hp.pos fun x hx => hexp x hx.1
  have hnorm : C1 ≤ Subgroup.normalizer (C2 : Set Q) := fun x hx =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => hab y hy.1 x hx.1)
  have hsup : Nat.card ↥(C1 ⊔ C2) ≤ Nat.card C1 * Nat.card C2 := by
    have h := Set.natCard_mul_le (s := (C1 : Set Q)) (t := (C2 : Set Q))
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right C1 C2 hnorm] at h
    exact h
  have h1 := Subgroup.card_le_of_le hle
  rw [hcard] at h1
  have h4 : p * p * p ≤ p * p * 1 := by
    rw [mul_one]
    calc p * p * p = p ^ 3 := by ring
      _ ≤ p * p := h1.trans (hsup.trans (Nat.mul_le_mul hC1 hC2))
  have h5 := Nat.le_of_mul_le_mul_left h4 (Nat.mul_pos hp.pos hp.pos)
  have := hp.two_le
  omega

end Irr

theorem a131Concl_of_isPGroup {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hr : CFSG.pRank p G ≤ 2) (H : Subgroup G) [H.Normal] (hH : IsPGroup p H)
    (hC : Subgroup.centralizer (CFSG.pCore p (G ⧸ H) : Set (G ⧸ H)) ≤ CFSG.pCore p (G ⧸ H)) :
    A131Concl p (G ⧸ H) := by
  classical
  have hinv : ∀ tb : G ⧸ H, orderOf tb = 2 →
      IsCyclic ↥(CFSG.pCore p (G ⧸ H) ⊓ Subgroup.centralizer ({tb} : Set (G ⧸ H))) :=
    fun tb htb => isCyclic_inf_centralizer hp hp2 hr H hH hC htb
  refine ⟨isCyclic_of_involutions hinv, pRank_two_le_two hp hp2 hC hinv,
    fun hel hcard hrank => ?_⟩
  by_contra hno
  have hirr : ∀ K : Subgroup (G ⧸ H), K.Normal → ⊥ < K → K < CFSG.pCore p (G ⧸ H) → False :=
    fun K hK h1 h2 => hno ⟨K, hK, h1, h2⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hrank
  obtain ⟨Tb, -, hTb, hTbc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (k := 2) (by omega)
      (H := (⊤ : Subgroup (G ⧸ H))) (p := 2)
  have hTbcard : (Tb : Set (G ⧸ H)).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hTbc
  obtain ⟨ab, habT, hab1⟩ : ∃ ab ∈ (Tb : Set (G ⧸ H)), ab ∉ ({1} : Set (G ⧸ H)) :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (by rw [hTbcard, Set.ncard_singleton]; omega)
      (Set.toFinite _)
  obtain ⟨bb, hbbT, hbb1⟩ : ∃ bb ∈ (Tb : Set (G ⧸ H)), bb ∉ ({1, ab} : Set (G ⧸ H)) :=
    Set.exists_mem_notMem_of_ncard_lt_ncard
      (by
        rw [hTbcard]
        exact (Set.ncard_insert_le _ _).trans_lt (by rw [Set.ncard_singleton]; omega))
      (Set.toFinite _)
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff, not_or] at hab1 hbb1
  have hab : orderOf ab = 2 := orderOf_eq_prime (hTb.2 ab habT) hab1
  have hbb : orderOf bb = 2 := orderOf_eq_prime (hTb.2 bb hbbT) hbb1.1
  have hcab : ab * bb = bb * ab := by
    have := hTb.1
    exact congrArg Subtype.val (this.is_comm.comm ⟨ab, habT⟩ ⟨bb, hbbT⟩)
  have hne : ab ≠ bb := fun h => hbb1.2 h.symm
  obtain ⟨tb, htbmem, hcent⟩ := exists_central_mod hp hp2 hr H hH hC hab hbb hcab hne
  have hab2 : ab * ab = 1 := by rw [← pow_two, ← hab, pow_orderOf_eq_one]
  have hbb2 : bb * bb = 1 := by rw [← pow_two, ← hbb, pow_orderOf_eq_one]
  have habb : orderOf (ab * bb) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · calc (ab * bb) ^ 2 = ab * (bb * ab) * bb := by rw [pow_two]; group
        _ = ab * (ab * bb) * bb := by rw [hcab]
        _ = (ab * ab) * (bb * bb) := by group
        _ = 1 := by rw [hab2, hbb2, mul_one]
    · intro h
      apply hne
      calc ab = ab * (bb * bb) := by rw [hbb2, mul_one]
        _ = (ab * bb) * bb := by group
        _ = bb := by rw [h, one_mul]
  rcases htbmem with rfl | rfl | rfl
  · exact false_of_irreducible hp hp2 hC hinv hel hcard hirr hab hbb hcab hne hcent
  · exact false_of_irreducible hp hp2 hC hinv hel hcard hirr hbb hab hcab.symm (Ne.symm hne)
      hcent
  · refine false_of_irreducible hp hp2 hC hinv hel hcard hirr habb hab ?_ ?_ hcent
    · calc ab * bb * ab = ab * (bb * ab) := by group
        _ = ab * (ab * bb) := by rw [hcab]
    · intro h
      apply hbb1.1
      calc bb = (ab * ab) * bb := by rw [hab2, one_mul]
        _ = ab * (ab * bb) := by group
        _ = 1 := by rw [h, hab2]

end CFSG.Quasithin.VolI.A131
