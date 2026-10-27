module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8HatDefs
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rF
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PerfectCoreCover
public import CFSG.Quasithin.H13.GoldschmidtC137SQL32
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Centralization

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PerfectCoreCover

theorem c8h_gl2_of_op {Γ : Type} [Group Γ] [Finite Γ] {d : Γ} {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hrank : pRank p (⊤ : Subgroup Γ) ≤ 2) (hd : orderOf d = 3)
    (hl3 : IsL3 (Γ ⧸ CFSG.pPrimeCore 3 Γ) 1)
    (hnot : ¬ CFSG.pCore p Γ ≤ centralizer ({d} : Set Γ)) :
    ∃ (ψ : Γ →* GL (Fin 2) (ZMod p)) (Oh Zh : Subgroup Γ)
      (φ : ↥Oh →* Multiplicative (Fin 2 → ZMod p)),
      ψ.ker ≤ CFSG.pPrimeCore 3 Γ ∧
      (∀ n ∈ ψ.ker, ¬ p ∣ orderOf n → n ∈ centralizer (CFSG.pCore p Γ : Set Γ)) ∧
      C8HatMod p d ψ Oh Zh φ := by
  classical
  let I := CFSG.pPrimeCore 3 Γ
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp1 : 1 < p := hp.one_lt
  have hsimple_card :=
    CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hl3
  haveI hsimple : IsSimpleGroup (Γ ⧸ I) := hsimple_card.1
  have hcard168 : Nat.card (Γ ⧸ I) = 168 := hsimple_card.2
  haveI hperf : Group.IsPerfect (Γ ⧸ I) := by
    apply TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative
    intro hc
    haveI : IsMulCommutative (Γ ⧸ I) := hc
    have hpcard : (Nat.card (Γ ⧸ I)).Prime := Group.is_simple_iff_prime_card.mp hsimple
    rw [hcard168] at hpcard
    norm_num at hpcard
  obtain ⟨E, hEn, hEp, hEmap⟩ :=
    exists_perfect_normal_map_eq_top (QuotientGroup.mk' I) (QuotientGroup.mk'_surjective I)
  haveI hEpI : Group.IsPerfect ↥E := hEp
  have hcover : ∀ γ : Γ, ∃ e ∈ E, ∃ i ∈ I, γ = e * i := by
    intro γ
    have hmem : (QuotientGroup.mk' I) γ ∈ E.map (QuotientGroup.mk' I) := by
      rw [hEmap]
      exact Subgroup.mem_top _
    obtain ⟨e, he, heq⟩ := Subgroup.mem_map.1 hmem
    obtain ⟨z, hz, hze⟩ := (QuotientGroup.mk'_eq_mk' I).1 heq
    exact ⟨e, he, z, hz, hze.symm⟩
  have hK : ∀ {A : Type} [Group A] (f : Γ →* A) (i : Γ), i ∈ I → f d = f i → f d = 1 := by
    intro A _ f i hi hfi
    have h1 : orderOf (f d) ∣ 3 := hd ▸ orderOf_map_dvd f d
    have hcop : Nat.Coprime 3 (Nat.card I) := CFSG.pPrimeCore_coprime_card
    have hcop' : Nat.Coprime (orderOf (f d)) (Nat.card I) :=
      Nat.Coprime.coprime_dvd_left h1 hcop
    have h2 : orderOf (f d) ∣ Nat.card I := by
      rw [hfi]
      exact (orderOf_map_dvd f i).trans (Subgroup.orderOf_dvd_natCard I hi)
    exact orderOf_eq_one_iff.1 (hcop'.eq_one_of_dvd h2)
  have hK' : ∀ {A : Type} [Group A] (f : Γ →* A), f d ≠ 1 → f.ker ≤ I := by
    intro A _ f hfd x hx
    set N : Subgroup Γ := f.ker ⊔ I with hN
    have hNn : N.Normal := by
      show (f.ker ⊔ I).Normal
      infer_instance
    have hmapn : (N.map (QuotientGroup.mk' I)).Normal :=
      Subgroup.Normal.map hNn _ (QuotientGroup.mk'_surjective I)
    haveI hmapnI : (N.map (QuotientGroup.mk' I)).Normal := hmapn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' I)) with
      hbot | htop
    · have hNI : N ≤ I := by
        intro n hn
        have h1 : (QuotientGroup.mk' I) n ∈ N.map (QuotientGroup.mk' I) :=
          Subgroup.mem_map_of_mem _ hn
        rw [hbot] at h1
        rw [Subgroup.mem_bot] at h1
        exact (QuotientGroup.eq_one_iff n).1 h1
      exact hNI (Subgroup.mem_sup_left hx)
    · have hdmem : (QuotientGroup.mk' I) d ∈ N.map (QuotientGroup.mk' I) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hnN, hn_eq⟩ := Subgroup.mem_map.1 hdmem
      obtain ⟨z, hz, hnz⟩ := (QuotientGroup.mk'_eq_mk' I).1 hn_eq
      obtain ⟨k, hk, i, hi, hki⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := f.ker) (t := I)).1 hnN
      have hfd_eq : f d = f (i * z) := by
        rw [← hnz, ← hki, mul_assoc, map_mul, MonoidHom.mem_ker.1 hk, one_mul]
      exact absurd (hK (A := A) (f := f) (i * z) (I.mul_mem hi hz) hfd_eq) hfd
  let R : Subgroup Γ := CFSG.pCore p Γ
  have hRp : IsPGroup p ↥R := CFSG.pCore_isPGroup
  let α : Γ →* MulAut ↥R := MulAut.conjNormal
  have hα1 : α d ≠ 1 := by
    intro h
    apply hnot
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    have h1 : ((α d) ⟨x, hx⟩ : ↥R) = ⟨x, hx⟩ := by
      rw [h]
      rfl
    have h2 : d * x * d⁻¹ = x := by
      simpa [α] using congrArg (fun y : ↥R => (y : Γ)) h1
    calc d * x = (d * x * d⁻¹) * d := by group
      _ = x * d := by rw [h2]
  have hcop : Nat.Coprime (orderOf (α d)) p := by
    have h1 : orderOf (α d) ∣ 3 := hd ▸ orderOf_map_dvd α d
    have h2 : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (by omega)
    exact Nat.Coprime.coprime_dvd_left h1 h2
  obtain ⟨D, hDs, hfaith⟩ :=
    CFSG.Quasithin.exists_isSupercritical_faithful (P := ↥R) hp2 hRp
  haveI hDchar : D.Characteristic := hDs.characteristic
  have hDp : IsPGroup p ↥D := hRp.to_subgroup D
  have hDexp : ∀ x : ↥D, x ^ p = 1 := fun x =>
    Subtype.ext (by simpa using hDs.pow_eq_one (x : ↥R) x.2)
  let W := ↥D ⧸ frattini ↥D
  let ρ : Γ →* MulAut W := (CFSG.SectionRank.Ccomm.frattiniAction D).comp α
  obtain ⟨-, hWcomm, hWpow⟩ := CFSG.SectionRank.Ccomm.frattini_quotient_elementary hDp
  have hρd : ρ d ≠ 1 := by
    intro h
    apply hα1
    apply hfaith (α d) hcop
    intro x hx
    have hmem : α d ∈ (CFSG.SectionRank.Ccomm.frattiniAction D).ker := by
      rw [MonoidHom.mem_ker]
      simpa [ρ] using h
    exact (CFSG.Quasithin.mem_ker_frattiniAction_iff D (α d)).1 hmem x hx
  have hrO : CFSG.Open.pRank p (⊤ : Subgroup Γ) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hrank
  have hDrank : CFSG.Open.pRank p (⊤ : Subgroup ↥D) ≤ 2 :=
    (CFSG.SectionRank.pRank_top_le_of_injective hp1 (R.subtype.comp D.subtype)
      (R.subtype_injective.comp D.subtype_injective)).trans hrO
  obtain ⟨-, hW2⟩ := CFSG.SectionRank.Ccomm.rank_two_exponent_prime_order_bound
    hDp hDexp hDrank
  obtain ⟨k, hk⟩ := (hDp.to_quotient (frattini ↥D)).exists_card_eq
  have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hp1).1 (hk ▸ hW2)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hWcomm hWpow hk
  have hk2' : k = 2 := by
    by_contra hkne
    have hk1 : k ≤ 1 := by omega
    have hWcommAut : ∀ a b : MulAut W, a * b = b * a := by
      intro a b
      apply (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective
      rw [map_mul, map_mul]
      exact CFSG.SectionRank.Ccomm.GL_comm_of_le_one hk1 _ _
    have hE1 : ρ.comp E.subtype = 1 := by
      apply CFSG.SectionRank.Ccomm.perfect_hom_eq_one_of_range_comm
      intro a _ b _
      exact hWcommAut a b
    obtain ⟨e', he', i, hi, hd_eq⟩ := hcover d
    have hρe' : ρ e' = 1 := by
      have h1 := congrArg (fun f : ↥E →* MulAut W => f ⟨e', he'⟩) hE1
      simpa using h1
    have hρi : ρ d = ρ i := by
      rw [hd_eq, map_mul, hρe', one_mul]
    exact hρd (hK (A := MulAut W) (f := ρ) i hi hρi)
  subst hk2'
  let ψ : Γ →* GL (Fin 2) (ZMod p) :=
    ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom).comp ρ
  have hψd : ψ d ≠ 1 := by
    intro h
    apply hρd
    apply (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective
    simpa [ψ] using h
  have hker : ψ.ker ≤ I := hK' (A := GL (Fin 2) (ZMod p)) (f := ψ) hψd
  have hcent : ∀ n ∈ ψ.ker, ¬ p ∣ orderOf n → n ∈ centralizer (R : Set Γ) := by
    intro n hn hnp
    have hρn : ρ n = 1 := by
      have h1 : (CFSG.SectionRank.Ccomm.elemAutEquivGL e) (ρ n) = 1 := by
        have h2 : ψ n = 1 := hn
        simpa [ψ] using h2
      exact (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective (by simpa using h1)
    have hmem : α n ∈ (CFSG.SectionRank.Ccomm.frattiniAction D).ker := by
      rw [MonoidHom.mem_ker]
      simpa [ρ] using hρn
    have hfix : ∀ x ∈ D, x⁻¹ * α n x ∈ frattiniIn D :=
      (CFSG.Quasithin.mem_ker_frattiniAction_iff D (α n)).1 hmem
    have hcopn : Nat.Coprime (orderOf (α n)) p := by
      have h1 : orderOf (α n) ∣ orderOf n := orderOf_map_dvd α n
      have h2 : Nat.Coprime p (orderOf n) := hp.coprime_iff_not_dvd.2 hnp
      exact Nat.Coprime.coprime_dvd_left h1 h2.symm
    have hαn : α n = 1 := hfaith (α n) hcopn hfix
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 : ((α n) ⟨g, hg⟩ : ↥R) = ⟨g, hg⟩ := by
      rw [hαn]
      rfl
    have h2 : n * g * n⁻¹ = g := by
      simpa [α] using congrArg (fun y : ↥R => (y : Γ)) h1
    have h3 : n * g = g * n := by
      calc n * g = (n * g * n⁻¹) * n := by group
        _ = g * n := by rw [h2]
    exact h3.symm
  let Oh : Subgroup Γ := D.map R.subtype
  let Zh : Subgroup Γ := (frattiniIn D).map R.subtype
  let Φ : ↥D ≃* ↥Oh := D.equivMapOfInjective R.subtype R.subtype_injective
  let φ : ↥Oh →* Multiplicative (Fin 2 → ZMod p) :=
    ((e : W →* Multiplicative (Fin 2 → ZMod p)).comp
      (QuotientGroup.mk' (frattini ↥D))).comp Φ.symm.toMonoidHom
  have hfr : frattiniIn Oh = Zh :=
    CFSG.Quasithin.A37.frattiniIn_map_subtype R D
  have hZ : Zh = UC22.fratSub Oh := by
    rw [show Zh = frattiniIn Oh from hfr.symm]
    rfl
  haveI hOhChar : Oh.Characteristic := by
    show (D.map R.subtype).Characteristic
    infer_instance
  haveI hfrChar : (frattiniIn D).Characteristic := by
    show ((frattini ↥D).map D.subtype).Characteristic
    infer_instance
  haveI hZhChar : Zh.Characteristic := by
    show ((frattiniIn D).map R.subtype).Characteristic
    infer_instance
  have hzle : Zh ≤ Oh := by
    rw [hZ]
    exact UC22.fratSub_le Oh
  have hlecore : Oh ≤ CFSG.pCore p Γ := by
    show D.map R.subtype ≤ CFSG.pCore p Γ
    exact Subgroup.map_subtype_le D
  have hφ_apply : ∀ d : ↥D, φ (Φ d) = e ((QuotientGroup.mk' (frattini ↥D)) d) := by
    intro d
    show e ((QuotientGroup.mk' (frattini ↥D)) (Φ.symm (Φ d))) =
      e ((QuotientGroup.mk' (frattini ↥D)) d)
    rw [MulEquiv.symm_apply_apply]
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨w, hw⟩ := e.surjective y
    obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective (frattini ↥D) w
    obtain ⟨x, hx⟩ := Φ.symm.surjective q
    refine ⟨x, ?_⟩
    have h1 : Φ.symm x = q := hx
    calc φ x = e ((QuotientGroup.mk' (frattini ↥D)) (Φ.symm x)) := rfl
      _ = e ((QuotientGroup.mk' (frattini ↥D)) q) := by rw [h1]
      _ = e w := by rw [hq]
      _ = y := hw
  have hkerfield : ∀ x : ↥Oh, φ x = 1 ↔ (x : Γ) ∈ Zh := by
    intro x
    set y : ↥D := Φ.symm x with hy
    have hxΦ : Φ y = x := by
      rw [hy]
      exact Φ.apply_symm_apply x
    have hxval : (x : Γ) = R.subtype (D.subtype y) := by
      rw [← hxΦ]
      exact Subgroup.coe_equivMapOfInjective_apply D R.subtype R.subtype_injective y
    have hφx : φ x = e ((QuotientGroup.mk' (frattini ↥D)) y) := by
      rw [← hxΦ]
      exact hφ_apply y
    rw [hxval]
    constructor
    · intro hφ
      have h1 : (QuotientGroup.mk' (frattini ↥D)) y = 1 := by
        apply e.injective
        rw [map_one]
        rwa [hφx] at hφ
      have hyF : y ∈ frattini ↥D := (QuotientGroup.eq_one_iff y).1 h1
      show R.subtype (D.subtype y) ∈ Zh
      exact Subgroup.mem_map_of_mem R.subtype (Subgroup.mem_map_of_mem D.subtype hyF)
    · intro hmem
      have hmem' : R.subtype (D.subtype y) ∈ (frattiniIn D).map R.subtype := hmem
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hmem'
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 hz
      have hzy' : D.subtype w = D.subtype y := by
        rw [hwz]
        exact R.subtype_injective hzy
      have hwy : w = y := D.subtype_injective hzy'
      rw [hwy] at hw
      have h1 : (QuotientGroup.mk' (frattini ↥D)) y = 1 :=
        (QuotientGroup.eq_one_iff y).2 hw
      have h2 : e ((QuotientGroup.mk' (frattini ↥D)) y) = 1 := by rw [h1, map_one]
      rw [hφx]
      exact h2
  have hequiv : ∀ (γ x : Γ) (hx : x ∈ Oh) (hx' : γ * x * γ⁻¹ ∈ Oh),
      φ ⟨γ * x * γ⁻¹, hx'⟩ = Multiplicative.ofAdd
        (Matrix.mulVec (ψ γ : Matrix (Fin 2) (Fin 2) (ZMod p))
          (Multiplicative.toAdd (φ ⟨x, hx⟩))) := by
    intro γ x hx hx'
    obtain ⟨x', hx'D, rfl⟩ := Subgroup.mem_map.1 hx
    set d' : ↥D := ⟨x', hx'D⟩ with hd'
    have hΦd' : Φ d' = (⟨R.subtype x', hx⟩ : ↥Oh) := by
      apply Subtype.ext
      rw [Subgroup.coe_equivMapOfInjective_apply]
    have hφx : φ ⟨R.subtype x', hx⟩ =
        e ((QuotientGroup.mk' (frattini ↥D)) d') := by
      conv_lhs => rw [← hΦd']
      exact hφ_apply d'
    let dα : ↥D := MulAut.characteristic D (α γ) d'
    have hdα : (dα : ↥R) = (α γ) (d' : ↥R) := rfl
    have hαd' : ((α γ) (d' : ↥R) : Γ) = γ * R.subtype x' * γ⁻¹ := by
      simp [α, hd']
    have hΦα : Φ dα = (⟨γ * R.subtype x' * γ⁻¹, hx'⟩ : ↥Oh) := by
      apply Subtype.ext
      rw [Subgroup.coe_equivMapOfInjective_apply, hdα]
      exact hαd'
    have hφconj : φ ⟨γ * R.subtype x' * γ⁻¹, hx'⟩ =
        e ((QuotientGroup.mk' (frattini ↥D)) dα) := by
      conv_lhs => rw [← hΦα]
      exact hφ_apply dα
    rw [hφx, hφconj]
    have hρ_apply : ∀ γ : Γ, ρ γ = (CFSG.SectionRank.Ccomm.frattiniAction D) (α γ) :=
      fun γ => rfl
    have hmv := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e (ρ γ)
      ((QuotientGroup.mk' (frattini ↥D)) d')
    rw [hρ_apply γ] at hmv
    have hfr' : (CFSG.SectionRank.Ccomm.frattiniAction D) (α γ)
        ((QuotientGroup.mk' (frattini ↥D)) d') =
          (QuotientGroup.mk' (frattini ↥D)) dα :=
      CFSG.SectionRank.Ccomm.frattiniAction_mk D (α γ) d'
    rw [hfr'] at hmv
    rw [show (ψ γ : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      (CFSG.SectionRank.Ccomm.elemAutEquivGL e (ρ γ) : Matrix (Fin 2) (Fin 2) (ZMod p))
      from rfl]
    rw [hρ_apply γ]
    rw [hmv]
    simp
  have hngen : ∀ H : Subgroup Γ, H ≤ Oh → H ⊔ Zh = Oh → H = Oh := by
    intro H hH h
    rw [hZ] at h
    exact UC22.eq_of_sup_fratSub_eq hH h
  have hdact : ¬ Oh ≤ centralizer ({d} : Set Γ) := by
    intro hle
    apply hα1
    apply hfaith (α d) hcop
    intro x hx
    have hxOh : ((x : ↥R) : Γ) ∈ Oh := Subgroup.mem_map_of_mem R.subtype hx
    have hcomm : ((x : ↥R) : Γ) ∈ centralizer ({d} : Set Γ) := hle hxOh
    have hxd : d * (x : Γ) = (x : Γ) * d :=
      (Subgroup.mem_centralizer_iff.1 hcomm) d (by simp)
    have hαx : ((α d) (⟨x, hx⟩ : ↥D) : ↥R) = x := by
      apply Subtype.ext
      simp only [α, MulAut.conjNormal_apply]
      calc d * (x : Γ) * d⁻¹ = ((x : Γ) * d) * d⁻¹ := by rw [hxd]
        _ = (x : Γ) := by group
    have h1 : x⁻¹ * (α d) (⟨x, hx⟩ : ↥D) = 1 := by rw [hαx, inv_mul_cancel]
    rw [h1]
    exact (frattiniIn D).one_mem
  refine ⟨ψ, Oh, Zh, φ, hker, hcent, ?_⟩
  exact ⟨inferInstance, inferInstance, hzle, hlecore, hsurj, hkerfield, hequiv, hngen, hdact⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
