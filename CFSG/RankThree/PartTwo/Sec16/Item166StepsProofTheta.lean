module

public import CFSG.RankThree.PartTwo.Sec16.Item166Proof
import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofSz
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.RankThree.PartTwo.Sec3.TwoGroupPrimeFiveAction
import CFSG.LocalAnalysis.SectionRank.SuzukiCover
import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingSelectedBase
import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
open CFSG.Blueprint CFSG.LieType.Ree
open scoped Pointwise commutatorElement

namespace Steps166

section Generic

variable {G : Type*} [Group G]

@[expose] noncomputable def resAut {Q : Type*} [Group Q] (D : Subgroup Q) [hD : D.Characteristic] :
    MulAut Q →* MulAut D where
  toFun σ := (σ.subgroupMap D).trans
    (MulEquiv.subgroupCongr (Subgroup.characteristic_iff_map_eq.mp hD σ))
  map_one' := MulEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext rfl

theorem exists_mul_mem_normalizer_of_sylow [Finite G] {p : ℕ} [Fact p.Prime] {A V : Subgroup G}
    (P : Sylow p A) (hP : (P : Subgroup A).map A.subtype = V) {j : G}
    (hj : j ∈ Subgroup.normalizer (A : Set G)) :
    ∃ c ∈ A, c * j ∈ Subgroup.normalizer (V : Set G) := by
  have hVA : V ≤ A := hP ▸ Subgroup.map_subtype_le _
  have hPV : (P : Subgroup A) = V.subgroupOf A := by
    rw [← hP, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
  have hAnorm : ∀ x ∈ A, j * x * j⁻¹ ∈ A := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hj x).mp hx
  set V₁ := V.map (MulAut.conj j).toMonoidHom with hV₁
  have hV₁A : V₁ ≤ A := by
    rintro _ ⟨v, hv, rfl⟩
    exact hAnorm v (hVA hv)
  have hV₁card : Nat.card (V₁.subgroupOf A) = Nat.card (P : Subgroup A) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₁A).toEquiv, hV₁,
      Subgroup.card_map_of_injective (MulAut.conj j).injective, ← hP,
      Subgroup.card_map_of_injective A.subtype_injective]
  let S₁ : Sylow p A := Sylow.ofCard (V₁.subgroupOf A) (by
    rw [hV₁card, Sylow.card_eq_multiplicity])
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq A S₁ P
  refine ⟨c, c.2, ?_⟩
  have hsub : ∀ v ∈ V, ((c : G) * j) * v * ((c : G) * j)⁻¹ ∈ V := by
    intro v hv
    have hmem : (⟨j * v * j⁻¹, hV₁A ⟨v, hv, rfl⟩⟩ : A) ∈ (S₁ : Subgroup A) := by
      change _ ∈ V₁.subgroupOf A
      rw [Subgroup.mem_subgroupOf]
      exact ⟨v, hv, rfl⟩
    have hmem' : MulAut.conj c • (⟨j * v * j⁻¹, hV₁A ⟨v, hv, rfl⟩⟩ : A) ∈
        ((c • S₁ : Sylow p A) : Subgroup A) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hmem
    rw [hc, hPV, Subgroup.mem_subgroupOf] at hmem'
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hmem'
    have he : ((c : G) * j) * v * ((c : G) * j)⁻¹ = c * (j * v * j⁻¹) * (c : G)⁻¹ := by
      group
    rw [he]
    exact hmem'
  exact Sec3.mem_normalizer_of_forall_conj_mem hsub

end Generic

section Faithful

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem le_or_eq_top_of_simple [Group.IsPerfect H] {θ C : Subgroup H} [θ.Normal] [C.Normal]
    (hθ : Group.IsSolvable θ) (hs : IsSimpleGroup (H ⧸ θ)) : C ≤ θ ∨ C = ⊤ := by
  have hmap : (C.map (QuotientGroup.mk' θ)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective θ)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map (QuotientGroup.mk' θ)) with h0 | h1
  · left
    intro x hx
    have : QuotientGroup.mk' θ x ∈ C.map (QuotientGroup.mk' θ) := ⟨x, hx, rfl⟩
    rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · right
    have hCθ : C ⊔ θ = ⊤ := by
      have := congrArg (Subgroup.comap (QuotientGroup.mk' θ)) h1
      rwa [Subgroup.comap_top, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
    set π := QuotientGroup.mk' C with hπ
    have hθmap : θ.map π = ⊤ := by
      have hC0 : C.map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
      calc θ.map π = C.map π ⊔ θ.map π := by rw [hC0, bot_sup_eq]
        _ = (C ⊔ θ).map π := (Subgroup.map_sup C θ π).symm
        _ = ⊤ := by
          rw [hCθ, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
          exact QuotientGroup.mk'_surjective C
    have hsurj : Function.Surjective (π.comp θ.subtype) := by
      rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype, hθmap]
    have hsol : Group.IsSolvable (H ⧸ C) := Group.isSolvable_of_surjective hsurj
    by_contra hne
    have : Nontrivial (H ⧸ C) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      apply hne
      exact eq_top_iff.mpr fun x _ => (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
    exact Group.IsPerfect.not_isSolvable (H ⧸ C) hsol

@[expose] noncomputable def conjRestr {M : Type*} [Group M] [Finite M] (A : Subgroup M) (β : M)
    (hβ : ∀ α ∈ A, β * α * β⁻¹ ∈ A) : MulAut A :=
  ((MulAut.conj β).subgroupMap A).trans (MulEquiv.subgroupCongr
    (Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨α, hα, rfl⟩; exact hβ α hα)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj β).injective])))

theorem coe_conjRestr_apply {M : Type*} [Group M] [Finite M] (A : Subgroup M) (β : M)
    (hβ : ∀ α ∈ A, β * α * β⁻¹ ∈ A) (α : A) :
    ((conjRestr A β hβ α : A) : M) = β * α * β⁻¹ :=
  rfl

theorem coe_conjRestr_pow_apply {M : Type*} [Group M] [Finite M] (A : Subgroup M) (β : M)
    (hβ : ∀ α ∈ A, β * α * β⁻¹ ∈ A) (n : ℕ) (α : A) :
    (((conjRestr A β hβ ^ n) α : A) : M) = β ^ n * α * (β ^ n)⁻¹ := by
  induction n generalizing α with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, coe_conjRestr_apply, pow_succ]
    group

theorem false_of_noncentral_pCore [Group.IsPerfect H]
    {θ R : Subgroup H} [θ.Normal] [R.Normal] (hRθ : R ≤ θ) (hR2 : IsPGroup 2 R)
    (hθs : Group.IsSolvable θ) (hθ2 : ∀ x ∈ θ, IsPGroup 2 (Subgroup.zpowers x) → x ∈ R)
    {a : ℕ} (ha : 1 ≤ a) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ (2 * a + 1))
    (e : H ⧸ θ ≃* suzukiGroup a F) {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    {V : Subgroup (H ⧸ R)} [V.Normal] (hVq : IsPGroup q V)
    (hVc : Subgroup.centralizer (V : Set (H ⧸ R)) ≠ ⊤)
    (hloc : ∀ Q : Subgroup H, IsPGroup q Q → ∀ u : H, u ≠ 1 → IsPGroup 2 (Subgroup.zpowers u) →
      CFSG.pRank q ↥(Q ⊓ Subgroup.centralizer {u}) ≤ 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' R with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hsimple : IsSimpleGroup (H ⧸ θ) :=
    isSimpleGroup_of_suzukiModel ⟨rfl, a, ha, F, inferInstance, inferInstance, rfl, hF, ⟨e⟩⟩
  have hK2 : ∀ h : H, π h ∈ Subgroup.centralizer (V : Set (H ⧸ R)) → h ∈ θ := by
    set C := (Subgroup.centralizer (V : Set (H ⧸ R))).comap π with hC
    have : C.Normal := Subgroup.Normal.comap inferInstance π
    rcases le_or_eq_top_of_simple (C := C) hθs hsimple with hle | htop
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
  obtain ⟨S⟩ : Nonempty (Sylow q Vh) := inferInstance
  set Q : Subgroup H := (S : Subgroup Vh).map Vh.subtype with hQ
  have hQq : IsPGroup q Q := S.isPGroup'.map Vh.subtype
  have hVQ : ∀ v ∈ V, ∃ x ∈ Q, π x = v := by
    let f : Vh →* V := (π.comp Vh.subtype).codRestrict V fun x => x.2
    have hf : Function.Surjective f := by
      rintro ⟨v, hv⟩
      obtain ⟨h, rfl⟩ := hπs v
      exact ⟨⟨h, hv⟩, rfl⟩
    have htop : ((S.mapSurjective hf : Sylow q V) : Subgroup V) = ⊤ :=
      ((S.mapSurjective hf).is_maximal' (hVq.to_subgroup ⊤) le_top).symm
    intro v hv
    have hmem : (⟨v, hv⟩ : V) ∈ ((S.mapSurjective hf : Sylow q V) : Subgroup V) :=
      htop ▸ Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hmem
    obtain ⟨s, hs, hsv⟩ := hmem
    exact ⟨s, ⟨s, hs, rfl⟩, congrArg Subtype.val hsv⟩
  have hK1 : ∀ n : H, n ∈ Subgroup.centralizer (Q : Set H) →
      π n ∈ Subgroup.centralizer (V : Set (H ⧸ R)) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hVQ v hv
    rw [← map_mul, ← map_mul, hn x hx]
  have hRQ : R ⊓ Q = ⊥ :=
    (IsPGroup.disjoint_of_ne 2 q (Ne.symm hq2) R Q hR2 hQq).eq_bot
  have hRN : ∀ r ∈ R, r ∈ Subgroup.normalizer (Q : Set H) →
      r ∈ Subgroup.centralizer (Q : Set H) := by
    intro r hr hrN
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : r * x * r⁻¹ * x⁻¹ ∈ Q :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hrN x).mp hx) (inv_mem hx)
    have h2 : r * x * r⁻¹ * x⁻¹ ∈ R := by
      have : x * r⁻¹ * x⁻¹ ∈ R := (inferInstance : R.Normal).conj_mem _ (inv_mem hr) x
      have e1 : r * x * r⁻¹ * x⁻¹ = r * (x * r⁻¹ * x⁻¹) := by group
      rw [e1]
      exact mul_mem hr this
    have h3 : r * x * r⁻¹ * x⁻¹ = 1 := by
      have : r * x * r⁻¹ * x⁻¹ ∈ R ⊓ Q := ⟨h2, h1⟩
      rwa [hRQ, Subgroup.mem_bot] at this
    calc x * r = (r * x * r⁻¹ * x⁻¹)⁻¹ * (r * x) := by group
      _ = r * x := by rw [h3, inv_one, one_mul]
  have hK3 : ∀ t ∈ θ, IsPGroup 2 (Subgroup.zpowers t) →
      t ∈ Subgroup.normalizer (Q : Set H) → t ∈ Subgroup.centralizer (Q : Set H) :=
    fun t ht ht2 htN => hRN t (hθ2 t ht ht2) htN
  have hFrat : ∀ h : H, ∃ n ∈ Subgroup.normalizer (Q : Set H), ∃ r ∈ R, n * r = h := by
    have htop := Sylow.normalizer_sup_eq_top S
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
  set ψ : H →* suzukiGroup a F := e.toMonoidHom.comp (QuotientGroup.mk' θ) with hψ
  have hψker : ∀ h : H, ψ h = 1 ↔ h ∈ θ := by
    intro h
    simp only [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hψsurjN : ∀ s : suzukiGroup a F, ∃ n ∈ Subgroup.normalizer (Q : Set H), ψ n = s := by
    intro s
    obtain ⟨g, hg⟩ := e.surjective s
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective θ g
    obtain ⟨n, hn, r, hr, rfl⟩ := hFrat h
    refine ⟨n, hn, ?_⟩
    have h1 : ψ (n * r) = s := hg
    rwa [map_mul, (hψker r).mpr (hRθ hr), mul_one] at h1
  have hQnt : Nontrivial Q := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hVc
    rw [eq_top_iff]
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hVQ v hv
    have : (⟨x, hx⟩ : Q) = 1 := Subsingleton.elim _ _
    have hx1 : x = 1 := congrArg Subtype.val this
    rw [hx1, map_one, one_mul, mul_one]
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hq2 hQq
  set cQ := Q.normalizerMonoidHom with hcQ
  have hcQ_apply : ∀ (n : Subgroup.normalizer (Q : Set H)) (x : Q),
      ((cQ n x : Q) : H) = (n : H) * x * (n : H)⁻¹ :=
    fun n x => Subgroup.normalizerMonoidHom_apply_apply_coe Q n x
  set ρD : Subgroup.normalizer (Q : Set H) →* MulAut D := (resAut D).comp cQ with hρD
  have hρD_apply : ∀ (n : Subgroup.normalizer (Q : Set H)) (d : D),
      (((ρD n d : D) : Q) : H) = (n : H) * ((d : Q) : H) * (n : H)⁻¹ :=
    fun n d => hcQ_apply n d
  have hcrit : ∀ n : Subgroup.normalizer (Q : Set H), IsPGroup 2 (Subgroup.zpowers (n : H)) →
      ρD n = 1 → (n : H) ∈ Subgroup.centralizer (Q : Set H) := by
    intro n hn2 hn1
    have hfixσ : cQ n ∈ fixingSubgroup (MulAut Q) (D : Set Q) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      have h := congrArg (fun σ : MulAut D => ((σ ⟨y, hy⟩ : D) : Q)) hn1
      exact h
    obtain ⟨k, hk⟩ := hDfix ⟨cQ n, hfixσ⟩
    obtain ⟨j, hj⟩ := hn2 ⟨(n : H), Subgroup.mem_zpowers _⟩
    have hk' : cQ n ^ q ^ k = 1 := congrArg Subtype.val hk
    have hj' : (n : H) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hj'' : cQ n ^ 2 ^ j = 1 := by
      rw [← map_pow]
      have : n ^ 2 ^ j = 1 := Subtype.ext (by simpa using hj')
      rw [this, map_one]
    have hcop : Nat.Coprime (q ^ k) (2 ^ j) :=
      Nat.Coprime.pow k j ((Nat.coprime_primes hq.out Nat.prime_two).mpr hq2)
    have hord : orderOf (cQ n) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
        (orderOf_dvd_of_pow_eq_one hj'')
    rw [orderOf_eq_one_iff] at hord
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := congrArg (fun σ : MulAut Q => ((σ ⟨x, hx⟩ : Q) : H)) hord
    simp only [MulAut.one_apply, hcQ_apply] at h
    calc x * (n : H) = ((n : H) * x * (n : H)⁻¹) * n := by rw [h]
      _ = n * x := by group
  have hρD_one : ∀ n : Subgroup.normalizer (Q : Set H),
      (n : H) ∈ Subgroup.centralizer (Q : Set H) → ρD n = 1 := by
    intro n hn
    refine MulEquiv.ext fun d => Subtype.ext (Subtype.ext ?_)
    rw [hρD_apply, MulAut.one_apply]
    have := Subgroup.mem_centralizer_iff.mp hn ((d : Q) : H) (d : Q).2
    rw [← this, mul_inv_cancel_right]
  obtain ⟨p, hp, hp3, t, htp, htN, htfix⟩ := exists_frobenius_pair (K := F) ha hF
  set Z := suzukiZ0 a F with hZ
  set NA : Subgroup H := Z.comap ψ ⊓ Subgroup.normalizer (Q : Set H) with hNA
  obtain ⟨P⟩ : Nonempty (Sylow 2 NA) := inferInstance
  set Ah : Subgroup H := (P : Subgroup NA).map NA.subtype with hAh
  have hAhNA : Ah ≤ NA := Subgroup.map_subtype_le _
  have hAh2 : IsPGroup 2 Ah := P.isPGroup'.map NA.subtype
  have hAhN : Ah ≤ Subgroup.normalizer (Q : Set H) := hAhNA.trans inf_le_right
  have hZ2 : IsPGroup 2 Z := fun z => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, suzukiZ0_sq hF z.2, Subgroup.coe_one])⟩
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
  obtain ⟨c, hc, hyAh⟩ := exists_mul_mem_normalizer_of_sylow P rfl hy₀NA
  set y := c * y₀ with hydef
  have hyN : y ∈ Subgroup.normalizer (Q : Set H) := mul_mem hc.2 hy₀N
  have hψc : ψ c ∈ Z := hc.1
  have hconj : ∀ z ∈ Z, ψ y * z * (ψ y)⁻¹ = t * z * t⁻¹ := by
    intro z hz
    have htz : t * z * t⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp htN z).mp hz
    rw [hydef, map_mul, hy₀, mul_inv_rev]
    calc ψ c * t * z * (t⁻¹ * (ψ c)⁻¹) = ψ c * (t * z * t⁻¹) * (ψ c)⁻¹ := by group
      _ = (t * z * t⁻¹) * ψ c * (ψ c)⁻¹ := by rw [suzukiZ0_comm hF hψc htz]
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
  set f : Ah →* MulAut D := ρD.comp (Subgroup.inclusion hAhN) with hf
  have hf_apply : ∀ x : Ah, f x = ρD ⟨x, hAhN x.2⟩ := fun x => rfl
  have hKT : ∀ x : Ah, ψ x = 1 → f x = 1 := by
    intro x hx
    have hxθ : (x : H) ∈ θ := (hψker x).mp hx
    have hx2 : IsPGroup 2 (Subgroup.zpowers (x : H)) :=
      hAh2.to_le (Subgroup.zpowers_le.mpr x.2)
    exact hρD_one _ (hK3 x hxθ hx2 (hAhN x.2))
  have hTK : ∀ x : Ah, f x = 1 → ψ x = 1 := by
    intro x hx
    have hx2 : IsPGroup 2 (Subgroup.zpowers (x : H)) :=
      hAh2.to_le (Subgroup.zpowers_le.mpr x.2)
    have hc := hcrit ⟨x, hAhN x.2⟩ hx2 hx
    exact (hψker x).mpr (hK2 x (hK1 x hc))
  set Ab : Subgroup (MulAut D) := f.range with hAb
  have hfmul : ∀ x x' : Ah, ψ x = ψ x' → f x = f x' := by
    intro x x' h
    have h1 : f (x * x'⁻¹) = 1 := hKT _ (by
      change ψ ((x : H) * (x' : H)⁻¹) = 1
      rw [map_mul, map_inv, h, mul_inv_cancel])
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hAbcomm : ∀ α β : Ab, α * β = β * α := by
    rintro ⟨_, x, rfl⟩ ⟨_, x', rfl⟩
    apply Subtype.ext
    change f x * f x' = f x' * f x
    rw [← map_mul, ← map_mul]
    apply hfmul
    change ψ ((x : H) * x') = ψ ((x' : H) * x)
    rw [map_mul, map_mul]
    exact suzukiZ0_comm hF (hAhNA x.2).1 (hAhNA x'.2).1
  let _ : CommGroup Ab := { (inferInstance : Group Ab) with mul_comm := hAbcomm }
  have hAb2 : ∀ α : Ab, α ^ 2 = 1 := by
    rintro ⟨_, x, rfl⟩
    apply Subtype.ext
    change f x ^ 2 = 1
    rw [← map_pow]
    apply hKT
    change ψ ((x : H) ^ 2) = 1
    rw [map_pow]
    exact suzukiZ0_sq hF (hAhNA x.2).1
  have hAbnt : Nontrivial Ab := by
    obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (suzukiZ0_ne_bot (a := a) hF)
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    obtain ⟨x, hx, hxz⟩ := hψAh z hz
    refine ⟨⟨⟨f ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩, 1, fun h => hz1' ?_⟩⟩
    have h1 : f ⟨x, hx⟩ = 1 := congrArg Subtype.val h
    rw [← hxz]
    exact hTK _ h1
  have hfix : ∀ α : Ab, α ≠ 1 → CFSG.pRank q ↥(fixedSubgroupOf (Ab.subtype α)) ≤ 2 := by
    rintro ⟨_, x, rfl⟩ hα
    have hx1 : (x : H) ≠ 1 := by
      intro h
      apply hα
      apply Subtype.ext
      change f x = 1
      have : x = 1 := Subtype.ext h
      rw [this, map_one]
    have hx2 : IsPGroup 2 (Subgroup.zpowers (x : H)) :=
      hAh2.to_le (Subgroup.zpowers_le.mpr x.2)
    set Fx := fixedSubgroupOf (Ab.subtype ⟨f x, x, rfl⟩) with hFx
    let g : Fx →* ↥(Q ⊓ Subgroup.centralizer {(x : H)}) :=
      ((Q.subtype.comp D.subtype).comp Fx.subtype).codRestrict _ fun d => by
        refine Subgroup.mem_inf.mpr ⟨((d : D) : Q).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have hd : f x d = d := d.2
        have h1 := congrArg (fun d' : D => ((d' : Q) : H)) hd
        simp only [hf_apply, hρD_apply] at h1
        change ((d : D) : Q) * (x : H) = (x : H) * ((d : D) : Q)
        calc ((d : D) : Q) * (x : H) = ((x : H) * ((d : D) : Q) * (x : H)⁻¹) * x := by rw [h1]
          _ = (x : H) * ((d : D) : Q) := by group
    have hg : Function.Injective g := by
      intro d₁ d₂ h
      have h' := congrArg (fun w : ↥(Q ⊓ Subgroup.centralizer {(x : H)}) => (w : H)) h
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
    exact (CFSG.RankThree.OddKernel.pRank_le_of_injective hq.out.one_lt g hg).trans
      (hloc Q hQq x hx1 hx2)
  set β : MulAut D := ρD ⟨y, hyN⟩ with hβ
  have hyAh' : ∀ x ∈ Ah, y * x * y⁻¹ ∈ Ah := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hyAh x).mp hx
  have hβf : ∀ x : Ah, β * f x * β⁻¹ = f ⟨y * x * y⁻¹, hyAh' x x.2⟩ := by
    intro x
    rw [hβ, hf_apply, hf_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hβAb : ∀ α ∈ Ab, β * α * β⁻¹ ∈ Ab := by
    rintro _ ⟨x, rfl⟩
    rw [hβf]
    exact ⟨_, rfl⟩
  set γ : MulAut Ab := conjRestr Ab β hβAb with hγ
  have hγ_apply : ∀ α : Ab, ((γ α : Ab) : MulAut D) = β * α * β⁻¹ :=
    coe_conjRestr_apply Ab β hβAb
  have hγp : γ ^ p = 1 := by
    refine MulEquiv.ext fun α => Subtype.ext ?_
    rw [coe_conjRestr_pow_apply, MulAut.one_apply]
    obtain ⟨_, x, rfl⟩ := α
    change β ^ p * f x * (β ^ p)⁻¹ = f x
    have hβp : β ^ p = ρD (⟨y, hyN⟩ ^ p) := by rw [hβ, map_pow]
    have hyp : ∀ x' ∈ Ah, y ^ p * x' * (y ^ p)⁻¹ ∈ Ah := by
      intro x' hx'
      have hn : y ^ p ∈ Subgroup.normalizer (Ah : Set H) := Subgroup.pow_mem _ hyAh p
      exact (Subgroup.mem_normalizer_iff.mp hn x').mp hx'
    have h1 : β ^ p * f x * (β ^ p)⁻¹ = f ⟨y ^ p * x * (y ^ p)⁻¹, hyp x x.2⟩ := by
      rw [hβp, hf_apply, hf_apply, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1]
    apply hfmul
    change ψ (y ^ p * x * (y ^ p)⁻¹) = ψ x
    rw [map_mul, map_mul, map_inv, map_pow, hconj_pow p _ (hAhNA x.2).1, htp, one_mul, inv_one,
      mul_one]
  have hγfix : ∀ α : Ab, γ α = α → α = 1 := by
    rintro ⟨_, x, rfl⟩ hα
    have h1 : β * f x * β⁻¹ = f x := congrArg Subtype.val hα
    rw [hβf] at h1
    have h2 : ψ (y * x * y⁻¹) = ψ x := by
      have h3 : f (⟨y * x * y⁻¹, hyAh' x x.2⟩ * x⁻¹) = 1 := by
        rw [map_mul, h1, map_inv, mul_inv_cancel]
      have h4 := hTK _ h3
      change ψ (y * x * y⁻¹ * (x : H)⁻¹) = 1 at h4
      rwa [map_mul (f := ψ) (y * x * y⁻¹), map_inv, mul_inv_eq_one] at h4
    rw [map_mul, map_mul, map_inv, hconj (ψ x) (hAhNA x.2).1] at h2
    have h5 := htfix (ψ x) (hAhNA x.2).1 h2
    apply Subtype.ext
    exact hKT x h5
  have hDq : IsPGroup q D := hQq.to_subgroup D
  have hDexp' : ∀ x : D, x ^ q = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hDcl : commutator D ≤ Subgroup.center D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro u _ v _
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 : ⁅(u : Q), (v : Q)⁆ ∈ D ⊓ Subgroup.centralizer (D : Set Q) :=
      hDcomm (Subgroup.commutator_mem_commutator u.2 (Subgroup.mem_top _))
    have h2 := Subgroup.mem_centralizer_iff.mp h1.2 (w : Q) w.2
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] using h2
  exact Sec3.false_of_elemAbelian_action (p := q) hq2 hp hp3 hDq hDexp' hDcl hAb2 Ab.subtype
    Ab.subtype_injective hfix γ hγp hγfix β fun α => (hγ_apply α).symm

theorem le_of_map_le_center [Group.IsPerfect H] {θ R : Subgroup H} [θ.Normal] [R.Normal]
    (hRθ : R ≤ θ) (hodd : Odd (Nat.card (θ.map (QuotientGroup.mk' R))))
    (hc : θ.map (QuotientGroup.mk' R) ≤ Subgroup.center (H ⧸ R)) {m : ℕ} (hm : 0 < m)
    (e : H ⧸ θ ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : θ ≤ R := by
  set η : H ⧸ R →* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m :=
    e.toMonoidHom.comp (QuotientGroup.map R θ (MonoidHom.id H) hRθ) with hη
  have hηs : Function.Surjective η := by
    intro s
    obtain ⟨g, rfl⟩ := e.surjective s
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective θ g
    exact ⟨(h : H ⧸ R), rfl⟩
  have hker : η.ker = θ.map (QuotientGroup.mk' R) := by
    ext x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective R x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : (h : H ⧸ θ) = 1 := by
        have : e (h : H ⧸ θ) = 1 := hx
        rwa [MulEquiv.map_eq_one_iff] at this
      exact ⟨h, (QuotientGroup.eq_one_iff h).mp h1, rfl⟩
    · rintro ⟨h', hh', hh'h⟩
      have h1 : h'⁻¹ * h ∈ R := by
        rw [← QuotientGroup.eq]
        exact hh'h
      have h2 : h ∈ θ := by
        have := mul_mem hh' (hRθ h1)
        simpa using this
      change e (h : H ⧸ θ) = 1
      rw [(QuotientGroup.eq_one_iff h).mpr h2, map_one]
  have h0 := CFSG.SectionRank.suzuki_perfect_odd_cover_trivial m hm η hηs (hker ▸ hc)
    (hker ▸ hodd)
  rw [hker, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h0
  exact h0

end Faithful

section Fitting

theorem exists_pCore_centralizer_ne_top {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    [N.Normal] (hN : Group.IsSolvable N) (hc : ¬ N ≤ Subgroup.center X) :
    ∃ r : ℕ, r.Prime ∧
      Subgroup.centralizer (((CFSG.pCore r N).map N.subtype : Subgroup X) : Set X) ≠ ⊤ := by
  by_contra hcon
  push Not at hcon
  apply hc
  have hF : (⊤ : Subgroup N) ≤ Subgroup.centralizer (CFSG.fittingSubgroup N : Set N) := by
    apply CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores
    intro r x _ y hy
    have h1 : (x : X) ∈ Subgroup.centralizer
        (((CFSG.pCore r.1.1 N).map N.subtype : Subgroup X) : Set X) := by
      rw [hcon r.1.1 (Nat.prime_of_mem_primeFactors r.1.2)]
      exact Subgroup.mem_top _
    have h2 := Subgroup.mem_centralizer_iff.mp h1 (y : X) ⟨y, hy, rfl⟩
    exact Subtype.ext h2
  have hFtop : CFSG.fittingSubgroup N = ⊤ :=
    eq_top_iff.mpr (hF.trans (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hN))
  have hN' : N = ⨆ r : (Nat.card N).primeFactors.attach,
      (CFSG.pCore r.1.1 N).map N.subtype := by
    rw [← Subgroup.map_iSup, ← CFSG.fitting_eq_sup_pCore, hFtop, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have htop : (⊤ : Subgroup X) ≤ Subgroup.centralizer (N : Set X) := by
    rw [hN']
    apply CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
    intro r
    rw [hcon r.1.1 (Nat.prime_of_mem_primeFactors r.1.2)]
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top g)) n hn).symm

end Fitting

section Main

variable {H : Type} [Group H] [Finite H]

theorem pCore_two_eq_of_odd [Group.IsPerfect H] {n : ℕ}
    (hSz : SuzukiModel (H ⧸ aschbacherSolvableCore 3 H) 2 n)
    (hodd : ∀ x ∈ aschbacherSolvableCore 3 H, IsPGroup 2 (Subgroup.zpowers x) →
      x ∈ CFSG.pCore 2 H)
    (hloc : ∀ q : ℕ, q.Prime → 3 < q → ∀ Q : Subgroup H, IsPGroup q Q → ∀ u : H, u ≠ 1 →
      IsPGroup 2 (Subgroup.zpowers u) → CFSG.pRank q ↥(Q ⊓ Subgroup.centralizer {u}) ≤ 2) :
    CFSG.pCore 2 H = aschbacherSolvableCore 3 H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := aschbacherSolvableCore 3 H with hθdef
  set R := CFSG.pCore 2 H with hRdef
  obtain ⟨hθs, -, hθ3, -, -, -, hθmax⟩ :=
    solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  have hRθ : R ≤ θ := hθmax 2 Nat.prime_two (by norm_num)
  have hR2 : IsPGroup 2 R := CFSG.pCore_isPGroup
  refine le_antisymm hRθ ?_
  set π := QuotientGroup.mk' R with hπ
  set Θ := θ.map π with hΘ
  have hΘn : Θ.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective R)
  have hΘs : Group.IsSolvable Θ := Group.isSolvable_of_surjective (π.subgroupMap_surjective θ)
  have hΘ2 : ¬ 2 ∣ Nat.card Θ := by
    intro h2
    obtain ⟨⟨x, hx⟩, hx2⟩ := exists_prime_orderOf_dvd_card' 2 h2
    obtain ⟨h, hh, rfl⟩ := hx
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
    have hh2 : IsPGroup 2 (Subgroup.zpowers (h ^ m)) := by
      refine IsPGroup.of_card (n := k) ?_
      rw [Nat.card_zpowers, orderOf_pow' h hm.pos.ne', hkm, Nat.gcd_mul_left_left,
        Nat.mul_div_cancel _ hm.pos]
    have hhR : h ^ m ∈ R := hodd _ (pow_mem hh m) hh2
    have h1 : (⟨π h, ⟨h, hh, rfl⟩⟩ : Θ) ^ m = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← map_pow, Subgroup.coe_one, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hhR
    have h2' := orderOf_dvd_of_pow_eq_one h1
    rw [hx2] at h2'
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2')
  have hΘodd : Odd (Nat.card Θ) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hΘ2)
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := fun h3 => hθ3 (h3.trans (Subgroup.card_map_dvd θ π))
  have hcore_bot : ∀ r : ℕ, r.Prime → ¬ r ∣ Nat.card Θ → CFSG.pCore r Θ = ⊥ := by
    intro r hr hrΘ
    have : Fact r.Prime := ⟨hr⟩
    rw [← Subgroup.card_eq_one]
    rcases (CFSG.pCore_isPGroup (p := r) (G := Θ)).card_eq_or_dvd with h1 | h1
    · exact h1
    · exact absurd (h1.trans (Subgroup.card_subgroup_dvd_card _)) hrΘ
  by_contra hθR
  by_cases hc : Θ ≤ Subgroup.center (H ⧸ R)
  ·
    obtain ⟨m, hm, ⟨e⟩⟩ :=
      CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hSz
    exact hθR (le_of_map_le_center hRθ hΘodd hc (by omega) e)
  ·
    obtain ⟨q, hq, hqc⟩ := exists_pCore_centralizer_ne_top hΘs hc
    have : Fact q.Prime := ⟨hq⟩
    have hqΘ : q ∣ Nat.card Θ := by
      by_contra hqΘ
      apply hqc
      rw [hcore_bot q hq hqΘ, Subgroup.map_bot]
      exact eq_top_iff.mpr fun g _ => Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [(Subgroup.mem_bot).mp hh, one_mul, mul_one]
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact Nat.not_even_iff_odd.mpr hΘodd (even_iff_two_dvd.mpr hqΘ)
    have hq3 : q ≠ 3 := by
      rintro rfl
      exact hΘ3 hqΘ
    have hq3' : 3 < q := by
      have := hq.two_le
      omega
    obtain ⟨-, a, ha, F, _, _, hn, hF, ⟨e⟩⟩ := hSz
    rw [hn] at hF
    have : ((CFSG.pCore q Θ).map Θ.subtype).Normal := inferInstance
    exact false_of_noncentral_pCore hRθ hR2 hθs hodd ha hF e hq2
      (CFSG.pCore_isPGroup.map Θ.subtype) hqc (hloc q hq hq3')

end Main

theorem pRank_inf_centralizer_le_two {G : Type} [Group G] [Finite G] (hG : TheoremFourHyp G)
    (K : Subgroup G) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (Q : Subgroup K) (u : K)
    (hu : u ≠ 1) (hu2 : IsPGroup 2 (Subgroup.zpowers u)) :
    CFSG.pRank q ↥(Q ⊓ Subgroup.centralizer {u}) ≤ 2 := by
  set QG := Q.map K.subtype with hQG
  let g : ↥(Q ⊓ Subgroup.centralizer {u}) →* ↥(QG ⊓ Subgroup.centralizer {(u : G)}) :=
    (K.subtype.comp (Q ⊓ Subgroup.centralizer {u}).subtype).codRestrict _ fun x => by
      refine Subgroup.mem_inf.mpr ⟨⟨x, (Subgroup.mem_inf.mp x.2).1, rfl⟩, ?_⟩
      have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h)
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun w : ↥(QG ⊓ Subgroup.centralizer {(u : G)}) =>
      (w : G)) h))
  have hu2G : IsPGroup 2 (Subgroup.zpowers (u : G)) := by
    have : Subgroup.zpowers (u : G) = (Subgroup.zpowers u).map K.subtype :=
      (MonoidHom.map_zpowers K.subtype u).symm
    rw [this]
    exact hu2.map K.subtype
  have hu1 : (u : G) ≠ 1 := fun h => hu (Subtype.ext h)
  have h1 := CFSG.RankThree.OddKernel.pRank_le_of_injective hq.one_lt g hg
  have h2 := CFSG.RankThree.PartOne.Lifting36.pRank_centralizer_le_localRank hq QG hu2G
    (Subgroup.mem_zpowers (u : G)) hu1
  have h3 := hG.localRank_lt q hq hq3
  omega

end Steps166

@[expose] def Step166ThetaTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], TheoremFourHyp G → ∀ X K : Subgroup G,
    K ∈ thetaComponentsIn X → ∀ n : ℕ,
      CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n →
        ∀ x ∈ aschbacherSolvableCore 3 ↥K, IsPGroup 2 (Subgroup.zpowers x) →
          x ∈ CFSG.pCore 2 ↥K

theorem step166Theta_of (h2 : Step166ThetaTwo) : Step166Theta := by
  intro G _ _ hG X K hK n hn
  have : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hK
  exact Steps166.pCore_two_eq_of_odd hn (h2 G hG X K hK n hn)
    fun q hq hq3 Q hQ u hu hu2 => Steps166.pRank_inf_centralizer_le_two hG K hq hq3 Q u hu hu2

end CFSG.RankThree.PartTwo.Sec16
