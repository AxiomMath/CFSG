module

public import CFSG.RankThree.PartTwo.Sec16.Item166Res2ProofTheta
import CFSG.RankThree.OddKernel.SimpleQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow1523Theta

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof166Res2
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem false_of_noncentral_pCore_frob [Group.IsPerfect H] {S : Type*} [Group S]
    [IsSimpleGroup S] (ψ : H →* S) (hψs : Function.Surjective ψ)
    (hθs : Group.IsSolvable ψ.ker) {R : Subgroup H} [R.Normal] (hRθ : R ≤ ψ.ker)
    {Z : Subgroup S} (hZ2 : IsPGroup 2 Z) (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hZ1 : Z ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp5 : p ≠ 5) {t : S}
    (htp : t ^ p = 1) (htN : t ∈ Subgroup.normalizer (Z : Set S))
    (htfix : ∀ z ∈ Z, t * z * t⁻¹ = z → z = 1)
    {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    {V : Subgroup (H ⧸ R)} [V.Normal] (hVq : IsPGroup q V)
    (hVc : Subgroup.centralizer (V : Set (H ⧸ R)) ≠ ⊤)
    (hloc : ∀ Q : Subgroup H, IsPGroup q Q → ∀ u : H, u ≠ 1 → IsPGroup 2 (Subgroup.zpowers u) →
      CFSG.pRank q ↥(Q ⊓ Subgroup.centralizer {u}) ≤ 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := ψ.ker with hθdef
  set π := QuotientGroup.mk' R with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hsimple : IsSimpleGroup (H ⧸ θ) :=
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).isSimpleGroup
  have hψker : ∀ h : H, ψ h = 1 ↔ h ∈ θ := fun h => (MonoidHom.mem_ker).symm
  have hK2 : ∀ h : H, π h ∈ Subgroup.centralizer (V : Set (H ⧸ R)) → h ∈ θ := by
    set C := (Subgroup.centralizer (V : Set (H ⧸ R))).comap π with hC
    have : C.Normal := Subgroup.Normal.comap inferInstance π
    rcases Steps166.le_or_eq_top_of_simple (C := C) hθs hsimple with hle | htop
    · exact fun h hh => hle hh
    · exfalso
      apply hVc
      rw [eq_top_iff]
      intro g _
      obtain ⟨h, rfl⟩ := hπs g
      have : h ∈ C := htop ▸ Subgroup.mem_top h
      exact this
  set Vh := V.comap π with hVh
  have : Vh.Normal := Subgroup.Normal.comap inferInstance π
  obtain ⟨Sq⟩ : Nonempty (Sylow q Vh) := inferInstance
  set Q : Subgroup H := (Sq : Subgroup Vh).map Vh.subtype with hQ
  have hQq : IsPGroup q Q := Sq.isPGroup'.map Vh.subtype
  have hVQ : ∀ v ∈ V, ∃ x ∈ Q, π x = v := by
    let f : Vh →* V := (π.comp Vh.subtype).codRestrict V fun x => x.2
    have hf : Function.Surjective f := by
      rintro ⟨v, hv⟩
      obtain ⟨h, rfl⟩ := hπs v
      exact ⟨⟨h, hv⟩, rfl⟩
    have htop : ((Sq.mapSurjective hf : Sylow q V) : Subgroup V) = ⊤ :=
      ((Sq.mapSurjective hf).is_maximal' (hVq.to_subgroup ⊤) le_top).symm
    intro v hv
    have hmem : (⟨v, hv⟩ : V) ∈ ((Sq.mapSurjective hf : Sylow q V) : Subgroup V) :=
      htop ▸ Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hmem
    obtain ⟨s, hs, hsv⟩ := hmem
    exact ⟨s, ⟨s, hs, rfl⟩, congrArg Subtype.val hsv⟩
  have hCQ : ∀ n : H, n ∈ Subgroup.centralizer (Q : Set H) → n ∈ θ := by
    intro n hn
    apply hK2
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hVQ v hv
    rw [← map_mul, ← map_mul, hn x hx]
  have hFrat : ∀ h : H, ∃ n ∈ Subgroup.normalizer (Q : Set H), ∃ r ∈ R, n * r = h := by
    have htop := Sylow.normalizer_sup_eq_top Sq
    have hVh : Vh ≤ Subgroup.normalizer (Q : Set H) ⊔ R := by
      intro h hh
      obtain ⟨x, hx, hxh⟩ := hVQ (π h) hh
      have hxR : x⁻¹ * h ∈ R := by
        rw [← QuotientGroup.eq]
        exact hxh
      have := Subgroup.mul_mem_sup (Subgroup.le_normalizer hx) hxR
      simpa using this
    intro h
    have hh : h ∈ Subgroup.normalizer (Q : Set H) ⊔ R := by
      have : h ∈ Subgroup.normalizer (Q : Set H) ⊔ Vh := by
        rw [hQ, htop]
        exact Subgroup.mem_top h
      exact (sup_le le_sup_left hVh) this
    exact Subgroup.mem_sup_of_normal_right.mp hh
  have hψsurjN : ∀ s : S, ∃ n ∈ Subgroup.normalizer (Q : Set H), ψ n = s := by
    intro s
    obtain ⟨h, rfl⟩ := hψs s
    obtain ⟨n, hn, r, hr, rfl⟩ := hFrat h
    refine ⟨n, hn, ?_⟩
    rw [map_mul, (hψker r).mpr (hRθ hr), mul_one]
  have : Fact p.Prime := ⟨hp⟩
  set NA : Subgroup H := Z.comap ψ ⊓ Subgroup.normalizer (Q : Set H) with hNA
  obtain ⟨P⟩ : Nonempty (Sylow 2 NA) := inferInstance
  set Ah : Subgroup H := (P : Subgroup NA).map NA.subtype with hAh
  have hAhNA : Ah ≤ NA := Subgroup.map_subtype_le _
  have hAh2 : IsPGroup 2 Ah := P.isPGroup'.map NA.subtype
  have hAhN : Ah ≤ Subgroup.normalizer (Q : Set H) := hAhNA.trans inf_le_right
  have hψAh : ∀ z ∈ Z, ∃ x ∈ Ah, ψ x = z := by
    let f : NA →* Z := (ψ.comp NA.subtype).codRestrict Z fun x => x.2.1
    have hf : Function.Surjective f := by
      rintro ⟨z, hz⟩
      obtain ⟨n, hn, hnz⟩ := hψsurjN z
      exact ⟨⟨n, (show ψ n ∈ Z from hnz ▸ hz), hn⟩, Subtype.ext hnz⟩
    have htop : ((P.mapSurjective hf : Sylow 2 Z) : Subgroup Z) = ⊤ :=
      ((P.mapSurjective hf).is_maximal' (hZ2.to_subgroup ⊤) le_top).symm
    intro z hz
    have hmem : (⟨z, hz⟩ : Z) ∈ ((P.mapSurjective hf : Sylow 2 Z) : Subgroup Z) :=
      htop ▸ Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hmem
    obtain ⟨s, hs, hsz⟩ := hmem
    exact ⟨s, ⟨s, hs, rfl⟩, congrArg Subtype.val hsz⟩
  obtain ⟨y₀, hy₀N, hy₀⟩ := hψsurjN t
  have hy₀NA : y₀ ∈ Subgroup.normalizer (NA : Set H) := by
    apply Sec3.mem_normalizer_of_forall_conj_mem
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · change ψ (y₀ * x * y₀⁻¹) ∈ Z
      rw [map_mul, map_mul, map_inv, hy₀]
      exact (Subgroup.mem_normalizer_iff.mp htN _).mp hx1
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy₀N hx2) (Subgroup.inv_mem _ hy₀N)
  obtain ⟨c, hc, hyAh⟩ := Steps166.exists_mul_mem_normalizer_of_sylow P rfl hy₀NA
  set y := c * y₀ with hydef
  have hyN : y ∈ Subgroup.normalizer (Q : Set H) := mul_mem hc.2 hy₀N
  have hψc : ψ c ∈ Z := hc.1
  have hconj : ∀ z ∈ Z, ψ y * z * (ψ y)⁻¹ = t * z * t⁻¹ := by
    intro z hz
    have htz : t * z * t⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp htN z).mp hz
    rw [hydef, map_mul, hy₀, mul_inv_rev]
    calc ψ c * t * z * (t⁻¹ * (ψ c)⁻¹) = ψ c * (t * z * t⁻¹) * (ψ c)⁻¹ := by group
      _ = (t * z * t⁻¹) * ψ c * (ψ c)⁻¹ := by rw [hZab _ hψc _ htz]
      _ = t * z * t⁻¹ := by group
  have hconj_pow : ∀ (k : ℕ), ∀ z ∈ Z, ψ y ^ k * z * (ψ y ^ k)⁻¹ = t ^ k * z * (t ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro z _; simp
    | succ k ih =>
      intro z hz
      have htz : t * z * t⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp htN z).mp hz
      calc ψ y ^ (k + 1) * z * (ψ y ^ (k + 1))⁻¹ = ψ y ^ k * (ψ y * z * (ψ y)⁻¹) *
            (ψ y ^ k)⁻¹ := by group
        _ = ψ y ^ k * (t * z * t⁻¹) * (ψ y ^ k)⁻¹ := by rw [hconj z hz]
        _ = t ^ k * (t * z * t⁻¹) * (t ^ k)⁻¹ := ih _ htz
        _ = t ^ (k + 1) * z * (t ^ (k + 1))⁻¹ := by group
  obtain ⟨b, m, hpm, hym⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' p hp.ne_one
  set y' := y ^ m with hy'def
  have hy'p : y' ^ (p ^ b) = 1 := by
    rw [hy'def, ← pow_mul, mul_comm, ← hym, pow_orderOf_eq_one]
  have hy'N : y' ∈ Subgroup.normalizer (Q : Set H) := pow_mem hyN m
  have hy'Ah : y' ∈ Subgroup.normalizer (Ah : Set H) := pow_mem hyAh m
  have hfpf : ∀ z ∈ Z, ψ y' * z * (ψ y')⁻¹ = z → z = 1 := by
    intro z hz h
    rw [hy'def, map_pow, hconj_pow m z hz] at h
    exact htfix z hz (commute_of_pow_commute hp hpm htp h)
  set X := Subgroup.zpowers y' with hXdef
  have hXp : IsPGroup p X := isPGroup_zpowers_of_pow_eq_one hy'p
  have hXAh : X ≤ Subgroup.normalizer (Ah : Set H) := Subgroup.zpowers_le.mpr hy'Ah
  have hXQ : X ≤ Subgroup.normalizer (Q : Set H) := Subgroup.zpowers_le.mpr hy'N
  set U := ⁅Ah, X⁆ with hUdef
  have hUAh : U ≤ Ah := Subgroup.le_normalizer_iff_commutator_le_left.mp hXAh
  have hU2 : IsPGroup 2 U := hAh2.to_le hUAh
  have hcopAh : ¬ p ∣ Nat.card Ah := by
    obtain ⟨k, hk⟩ := hAh2.exists_card_eq
    rw [hk]
    intro h
    have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    omega
  have hUX : ⁅U, X⁆ = U :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp X Ah hXp hcopAh
      hXAh
  have hUQ : U ≤ Subgroup.normalizer (Q : Set H) := hUAh.trans hAhN
  obtain ⟨u, huU, huC⟩ : ∃ u ∈ U, u ∉ Subgroup.centralizer (Q : Set H) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ1
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    obtain ⟨w, hwAh, hwz⟩ := hψAh z hz
    have hcw : ⁅w, y'⁆ ∈ U := Subgroup.commutator_mem_commutator hwAh (Subgroup.mem_zpowers y')
    have h1 : ψ ⁅w, y'⁆ = 1 := (hψker _).mpr (hCQ _ (hcon _ hcw))
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hwz] at h1
    apply hz1'
    apply hfpf z hz
    calc ψ y' * z * (ψ y')⁻¹ = (z * ψ y' * z⁻¹ * (ψ y')⁻¹)⁻¹ * z := by group
      _ = z := by rw [h1, inv_one, one_mul]
  set NQ := Subgroup.normalizer (Q : Set H) with hNQ
  let ρ : NQ →* MulAut Q := Q.normalizerMonoidHom
  have hρ_apply : ∀ (n : NQ) (w : Q), ((ρ n w : Q) : H) = (n : H) * w * (n : H)⁻¹ :=
    fun n w => Subgroup.normalizerMonoidHom_apply_apply_coe Q n w
  let G' := ↥Q ⋊[MonoidHom.id (MulAut ↥Q)] MulAut ↥Q
  have : Finite G' := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  let f : NQ →* G' := SemidirectProduct.inr.comp ρ
  set P' : Subgroup G' := (SemidirectProduct.inl : ↥Q →* G').range with hP'
  set U' : Subgroup G' := (U.subgroupOf NQ).map f with hU'
  set X' : Subgroup G' := (X.subgroupOf NQ).map f with hX'
  have hXsub : X.subgroupOf NQ = Subgroup.zpowers ⟨y', hy'N⟩ := by
    ext n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by rw [Subgroup.coe_zpow]⟩
  have hX'eq : X' = Subgroup.zpowers (f ⟨y', hy'N⟩) := by
    rw [hX', hXsub, MonoidHom.map_zpowers]
  have hP'q : IsPGroup q P' := by
    rw [hP', MonoidHom.range_eq_map]
    exact (hQq.to_subgroup ⊤).map _
  have hU'2 : IsPGroup 2 U' := (hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUQ).symm).map f
  have hX'p : IsPGroup p X' := (hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXQ).symm).map f
  have hU'X' : ⁅U', X'⁆ = U' := by
    rw [hU', hX', ← Subgroup.map_commutator, Sec3.commutator_subgroupOf hUQ hXQ, hUX]
  have hnorm : ∀ K : Subgroup G', K ≤ Subgroup.normalizer (P' : Set G') := by
    intro K
    have : P'.Normal := by
      rw [hP', SemidirectProduct.range_inl_eq_ker_rightHom]
      infer_instance
    rw [Subgroup.normalizer_eq_top_iff.mpr this]
    exact le_top
  have hρne : ρ ⟨u, hUQ huU⟩ ≠ 1 := by
    intro h1
    apply huC
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h2 := congrArg (fun σ : MulAut Q => ((σ ⟨w, hw⟩ : Q) : H)) h1
    simp only [MulAut.one_apply, hρ_apply] at h2
    calc w * u = (u * w * u⁻¹) * u := by rw [h2]
      _ = u * w := by group
  have hU'1 : U' ≠ ⊥ := by
    intro h0
    apply hρne
    have hmem : f ⟨u, hUQ huU⟩ ∈ U' := ⟨⟨u, hUQ huU⟩, huU, rfl⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact SemidirectProduct.inr_injective (hmem.trans (map_one _).symm)
  have hfaith : U' ⊓ Subgroup.centralizer (P' : Set G') = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨n, -, rfl⟩, hnC⟩
    rw [Subgroup.mem_bot]
    change SemidirectProduct.inr (ρ n) = 1
    rw [eq_one_of_inr_mem_centralizer hnC, map_one]
  have hfix : ∀ w ∈ U', w ≠ 1 →
      CFSG.Assembly.pRank q (P' ⊓ Subgroup.centralizer ({w} : Set G')) ≤ 2 := by
    rintro _ ⟨n, hn, rfl⟩ hw1
    have hnU : (n : H) ∈ U := hn
    have hn1 : (n : H) ≠ 1 := by
      intro h1
      apply hw1
      have : n = 1 := Subtype.ext h1
      rw [this, map_one]
    have hn2 : IsPGroup 2 (Subgroup.zpowers (n : H)) :=
      hU2.to_le (Subgroup.zpowers_le.mpr hnU)
    set C' := P' ⊓ Subgroup.centralizer ({f n} : Set G') with hC'
    have hleft : ∀ v : C', (v : G') = SemidirectProduct.inl (v : G').left := by
      rintro ⟨_, ⟨w, rfl⟩, -⟩
      rfl
    have hmemC : ∀ v : C', (((v : G').left : Q) : H) ∈ Q ⊓ Subgroup.centralizer {(n : H)} := by
      intro v
      refine ⟨((v : G').left).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hv := Subgroup.mem_centralizer_singleton_iff.mp v.2.2
      rw [hleft v] at hv
      have h1 := apply_eq_of_inl_mul_inr hv
      have h2 := congrArg (fun w : Q => (w : H)) h1
      simp only [hρ_apply] at h2
      calc (((v : G').left : Q) : H) * n
          = ((n : H) * ((v : G').left : Q) * (n : H)⁻¹) * n := by rw [h2]
        _ = n * (((v : G').left : Q) : H) := by group
    let g : C' →* ↥(Q ⊓ Subgroup.centralizer {(n : H)}) :=
      { toFun := fun v => ⟨(((v : G').left : Q) : H), hmemC v⟩
        map_one' := rfl
        map_mul' := by
          intro v₁ v₂
          apply Subtype.ext
          change ((((v₁ : G') * (v₂ : G')).left : Q) : H) = _
          rw [SemidirectProduct.mul_left]
          have hr : (v₁ : G').right = 1 := by rw [hleft v₁]; rfl
          rw [hr]
          rfl }
    have hg : Function.Injective g := by
      intro v₁ v₂ h
      have h0 : ((g v₁ : ↥(Q ⊓ Subgroup.centralizer {(n : H)})) : H) = (g v₂ : H) :=
        congrArg Subtype.val h
      have h1 : (v₁ : G').left = (v₂ : G').left := Subtype.ext h0
      apply Subtype.ext
      rw [hleft v₁, hleft v₂, h1]
    have h1 := CFSG.RankThree.OddKernel.pRank_le_of_injective hq.out.one_lt g hg
    have h2 := hloc Q hQq n hn1 hn2
    have h3 : CFSG.Assembly.pRank q C' = CFSG.pRank q ↥C' :=
      ((CFSG.SectionRank.pRank_eq_open_pRank_top q ↥C').trans
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup C').symm).symm
    rw [h3]
    exact h1.trans h2
  have h5 := rank3II_3_6_pow hq.out hq2 hp hp3 hP'q hU'2 hX'eq hX'p hU'X' hU'1 (hnorm U')
    (hnorm X') hfaith hfix
  exact hp5 h5

end CFSG.RankThree.PartTwo.Sec15.Sylow1523Theta
