module

public import CFSG.Quasithin.Vol2.Ch11SecOE4A
public import CFSG.Quasithin.Vol2.Ch11SecOE4C

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE4

open Subgroup CFSG.Quasithin
open CFSG.Open (pCoreOf quasithinIsSylowTwo)

variable {G : Type} [Group G] [Finite G]

theorem le_pow_or_le_of_invariant {T D : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hTD : T ≤ normalizer (D : Set G)) (hperf : ⁅D, D⁆ = D)
    {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (he : 1 ≤ e)
    (φ : ↥(CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)) ≃*
      (Multiplicative (ZMod (p ^ e)) × Multiplicative (ZMod (p ^ e))))
    (hcan : H13.NQCore.SNCanonical T D (H13.nqPrimeResidualX D p) p)
    (hIP : ∀ x ∈ iP D p, ∀ hxD : x ∈ D,
      QuotientGroup.mk' (CFSG.pCore 2 ↥D) ⟨x, hxD⟩ ∈ CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D))
    {C : Subgroup G} (hCI : C ≤ iP D p) (hTC : T ≤ normalizer (C : Set G))
    (hOC : pCoreOf 2 (iP D p) ≤ C) :
    (∀ c ∈ C, ∀ hcD : c ∈ D, ∃ w ∈ CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D),
        QuotientGroup.mk' (CFSG.pCore 2 ↥D) ⟨c, hcD⟩ = w ^ p) ∨ iP D p ≤ C := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥D) with hπ
  set P := CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) with hP
  have hPc : ∀ a b : ↥P, a * b = b * a := fun a b =>
    φ.injective (by rw [map_mul, map_mul, mul_comm])
  let _ : CommGroup ↥P := { (inferInstance : Group ↥P) with mul_comm := hPc }
  set ρD : ↥D →* MulAut ↥P := (pCoreAct D p).comp (inclusion le_normalizer) with hρD
  obtain ⟨hfr, -, -, hWcard, -, -, hker, -⟩ := H13.NQBlock.homocyclic_frattini_transport he φ ρD
  set β : ↥D →* MulAut (↥P ⧸ frattini ↥P) :=
    (CFSG.SectionRank.Ccomm.autQuotient (frattini ↥P)).comp ρD with hβdef
  have hβ : β ≠ 1 := by
    intro h1
    obtain ⟨d, hdD, hd⟩ := hcan.nontrivial
    apply hd
    have hmem : (⟨(d : G), hdD⟩ : ↥D) ∈ ((H13.NQBlock.omegaAut p).comp ρD).ker := by
      rw [← hker, MonoidHom.mem_ker]
      exact congrArg (fun f : ↥D →* MulAut (↥P ⧸ frattini ↥P) => f ⟨(d : G), hdD⟩) h1
    rw [MonoidHom.mem_ker] at hmem
    apply H13.NQCore.normalizerFrattiniConj_eq_one_of
    refine MulEquiv.ext fun w => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    have hyD : (y : G) ∈ D := hcan.le y.2
    have hyc : π ⟨(y : G), hyD⟩ ∈ closure {c | c ∈ P ∧ c ^ p = 1} := by
      rw [← hcan.image]
      exact ⟨⟨(y : G), hyD⟩, mem_subgroupOf.mpr y.2, rfl⟩
    have hyΩ : ∃ hyP : π ⟨(y : G), hyD⟩ ∈ P, (⟨_, hyP⟩ : ↥P) ^ p = 1 := by
      have hle : closure {c | c ∈ P ∧ c ^ p = 1} ≤
          ((powMonoidHom p : ↥P →* ↥P).ker).map P.subtype := by
        refine (closure_le _).mpr fun c hc => ⟨⟨c, hc.1⟩, ?_, rfl⟩
        show (⟨c, hc.1⟩ : ↥P) ∈ (powMonoidHom p : ↥P →* ↥P).ker
        rw [MonoidHom.mem_ker, powMonoidHom_apply]
        exact Subtype.ext hc.2
      obtain ⟨z, hz, hzy⟩ := hle hyc
      refine ⟨hzy ▸ z.2, ?_⟩
      have hz' : z = ⟨π ⟨(y : G), hyD⟩, hzy ▸ z.2⟩ := Subtype.ext hzy
      rw [← hz']
      exact (MonoidHom.mem_ker).mp hz
    obtain ⟨hyP, hyp⟩ := hyΩ
    have hfix := congrArg (fun f : MulAut ↥((powMonoidHom p : ↥P →* ↥P).ker) =>
      ((f ⟨⟨_, hyP⟩, (MonoidHom.mem_ker).mpr hyp⟩ : ↥P) : ↥D ⧸ CFSG.pCore 2 ↥D)) hmem
    simp only [MonoidHom.comp_apply, MulAut.one_apply] at hfix
    change π (D.normalizerMonoidHom ⟨(d : G), le_normalizer hdD⟩ ⟨(y : G), hyD⟩) =
      π ⟨(y : G), hyD⟩ at hfix
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      H13.NQBlock.mem_pCore_iff_mem_pCoreOf] at hfix
    show (QuotientGroup.mk ((H13.nqPrimeResidualX D p).normalizerMonoidHom d y) :
      ↥(H13.nqPrimeResidualX D p) ⧸ CFSG.pCore 2 ↥(H13.nqPrimeResidualX D p)) =
        QuotientGroup.mk y
    rw [QuotientGroup.eq, H13.NQBlock.mem_pCore_iff_mem_pCoreOf, ← hcan.inf_pCore]
    exact ⟨SetLike.coe_mem _, hfix⟩
  have hTJs : QuasithinUnique.IsSylowTwoOf T (normalizer (D : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hT hTD
  have hTDs : QuasithinUnique.IsSylowTwoOf (T ⊓ D) D :=
    A4.isSylowTwoOf_inf_normal hTJs le_normalizer le_rfl
  have hTDp : IsPGroup 2 ((T ⊓ D).subgroupOf D) :=
    hTDs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTDs.1).symm
  have hTDi : ¬ 2 ∣ ((T ⊓ D).subgroupOf D).index := hTDs.2.2
  set S : Sylow 2 ↥D := hTDp.toSylow hTDi with hS
  have hSc : (S : Subgroup ↥D) = (T ⊓ D).subgroupOf D := IsPGroup.toSylow_coe hTDp hTDi
  have : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hperf
  have hWc : IsMulCommutative (↥P ⧸ frattini ↥P) := ⟨⟨fun a b => mul_comm a b⟩⟩
  have hWp : ∀ w : ↥P ⧸ frattini ↥P, w ^ p = 1 := by
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hfr]
    exact ⟨y, rfl⟩
  set Cb : Subgroup ↥P := ((C.subgroupOf D).map π).comap P.subtype with hCb
  set M : Subgroup (↥P ⧸ frattini ↥P) := Cb.map (QuotientGroup.mk' (frattini ↥P)) with hM
  have hMinv : ∀ s ∈ (S : Subgroup ↥D), ∀ w ∈ M, β s w ∈ M := by
    intro s hs w hw
    rw [hSc, mem_subgroupOf] at hs
    obtain ⟨y, hy, rfl⟩ := hw
    obtain ⟨c, hc, hcy⟩ := hy
    refine ⟨ρD s y, ?_, rfl⟩
    refine ⟨D.normalizerMonoidHom ⟨(s : G), le_normalizer s.2⟩ c, ?_, ?_⟩
    · change (c : G) ∈ C at hc
      change (s : G) * (c : G) * (s : G)⁻¹ ∈ C
      exact (mem_normalizer_iff.mp (hTC hs.1) _).mp hc
    · have hy' : y = ⟨π c, hcy ▸ y.2⟩ := Subtype.ext hcy.symm
      rw [hy']
      rfl
  rcases SteinbergCD.perfect_sylow_two_irreducible_of_card_eq_sq hp5 hWp hWcard β hβ S M hMinv
    with h | h
  ·
    left
    intro c hc hcD
    have hcP := hIP c (hCI hc) hcD
    have hcCb : (⟨_, hcP⟩ : ↥P) ∈ Cb := ⟨⟨c, hcD⟩, mem_subgroupOf.mpr hc, rfl⟩
    have hle : Cb ≤ frattini ↥P := by
      rw [← QuotientGroup.ker_mk' (frattini ↥P), ← Subgroup.map_eq_bot_iff]
      exact h
    obtain ⟨w, hw⟩ := hfr ▸ hle hcCb
    refine ⟨(w : ↥D ⧸ CFSG.pCore 2 ↥D), w.2, ?_⟩
    have := congrArg Subtype.val hw
    simpa using this.symm
  ·
    right
    have hsup : Cb ⊔ frattini ↥P = ⊤ := by
      have h1 := comap_map_eq (QuotientGroup.mk' (frattini ↥P)) Cb
      rw [← hM, h, comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have htop : Cb = ⊤ := frattini_nongenerating hsup
    intro x hx
    have hxD := iP_le D p hx
    have hxCb : (⟨_, hIP x hx hxD⟩ : ↥P) ∈ Cb := htop ▸ mem_top _
    obtain ⟨c, hc, hcx⟩ := hxCb
    have hcC : (c : G) ∈ C := mem_subgroupOf.mp hc
    have h1 : π (c⁻¹ * ⟨x, hxD⟩) = 1 := by
      rw [map_mul, map_inv]
      change (π c)⁻¹ * π ⟨x, hxD⟩ = 1
      rw [hcx]
      exact inv_mul_cancel _
    have hcx' : (c : G)⁻¹ * x ∈ iP D p := mul_mem (inv_mem (hCI hcC)) hx
    have h2 := (mk_eq_one_iff hcx' (mul_mem (inv_mem c.2) hxD)).mp h1
    have e : x = (c : G) * ((c : G)⁻¹ * x) := by rw [mul_inv_cancel_left]
    rw [e]
    exact mul_mem hcC (hOC h2)

theorem commutator_mem_pCoreOf_of_pow {T D : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTD : T ≤ normalizer (D : Set G)) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (φ : ↥(CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)) ≃*
      (Multiplicative (ZMod (p ^ e)) × Multiplicative (ZMod (p ^ e))))
    (hIP : ∀ x ∈ iP D p, ∀ hxD : x ∈ D,
      QuotientGroup.mk' (CFSG.pCore 2 ↥D) ⟨x, hxD⟩ ∈ CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D))
    {t : G} (ht : t ∈ T)
    (h : ∀ x ∈ iP D p, ∀ hx : t * x * t⁻¹ * x⁻¹ ∈ D,
      ∃ w ∈ CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D),
        QuotientGroup.mk' (CFSG.pCore 2 ↥D) ⟨t * x * t⁻¹ * x⁻¹, hx⟩ = w ^ p) :
    ∀ x ∈ iP D p, t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 (iP D p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥D) with hπ
  set P := CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) with hP
  have hPc : ∀ a b : ↥P, a * b = b * a := fun a b =>
    φ.injective (by rw [map_mul, map_mul, mul_comm])
  let _ : CommGroup ↥P := { (inferInstance : Group ↥P) with mul_comm := hPc }
  have htD : t ∈ normalizer (D : Set G) := hTD ht
  set α := pCoreAct D p ⟨t, htD⟩ with hα
  obtain ⟨k, hk⟩ := hT.1 ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hαk : α ^ 2 ^ k = 1 := by
    rw [hα, ← map_pow]
    have : (⟨t, htD⟩ : ↥(normalizer (D : Set G))) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hexp : ∀ y : ↥P, y ^ p ^ e = 1 := H13.NQBlock.homocyclic_pow_prime_pow_eq_one φ
  have h1 : ∀ y : ↥P, α y * y⁻¹ ∈ (powMonoidHom p : ↥P →* ↥P).range := by
    intro y
    obtain ⟨r, hr, hrI⟩ := exists_mem_iP_of_mem_pCore hp y.2
    have hy : y = ⟨π r, hr ▸ y.2⟩ := Subtype.ext hr.symm
    have hcD : t * (r : G) * t⁻¹ * (r : G)⁻¹ ∈ D :=
      D.mul_mem ((mem_normalizer_iff.mp htD r).mp r.2) (D.inv_mem r.2)
    obtain ⟨w, hw, hwe⟩ := h r hrI hcD
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    rw [hy, powMonoidHom_apply]
    change w ^ p = π (D.normalizerMonoidHom ⟨t, htD⟩ r) * (π r)⁻¹
    rw [← hwe, ← map_inv, ← map_mul]
    rfl
  have hfix := apply_eq_of_mul_inv_mem_range_pow hcop hexp α hαk h1
  intro x hx
  have hxD := iP_le D p hx
  have hxP := hIP x hx hxD
  have h2 := congrArg Subtype.val (hfix ⟨_, hxP⟩)
  change π (D.normalizerMonoidHom ⟨t, htD⟩ ⟨x, hxD⟩) = π ⟨x, hxD⟩ at h2
  have hcI : t * x * t⁻¹ * x⁻¹ ∈ iP D p :=
    mul_mem ((mem_normalizer_iff.mp (normalizer_le_normalizer_iP D p htD) x).mp hx) (inv_mem hx)
  refine (mk_eq_one_iff hcI (iP_le D p hcI)).mp ?_
  change π (D.normalizerMonoidHom ⟨t, htD⟩ ⟨x, hxD⟩ * ⟨x, hxD⟩⁻¹) = 1
  rw [map_mul, map_inv, h2, mul_inv_cancel]

end CFSG.Quasithin.Vol2.Ch11.OE4
