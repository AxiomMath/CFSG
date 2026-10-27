module

public import CFSG.Quasithin.Background.BlueprintB2Reduced
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.H13.C1294

namespace IDIrr

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

section Membership

theorem mem_sup_of_comm {s t : Subgroup G} (hc : ∀ a ∈ s, ∀ b ∈ t, a * b = b * a) {x : G} :
    x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨x, hx, 1, t.one_mem, mul_one x⟩
      · exact ⟨1, s.one_mem, x, hx, one_mul x⟩
    | one => exact ⟨1, s.one_mem, 1, t.one_mem, one_mul 1⟩
    | mul x y _ _ hx' hy' =>
      obtain ⟨y1, hy1, z1, hz1, rfl⟩ := hx'
      obtain ⟨y2, hy2, z2, hz2, rfl⟩ := hy'
      refine ⟨y1 * y2, s.mul_mem hy1 hy2, z1 * z2, t.mul_mem hz1 hz2, ?_⟩
      have h := hc y2 hy2 z1 hz1
      have e : y1 * y2 * (z1 * z2) = y1 * (y2 * z1) * z2 := by group
      rw [e, h]
      group
    | inv x _ hx' =>
      obtain ⟨y, hy, z, hz, rfl⟩ := hx'
      refine ⟨y⁻¹, s.inv_mem hy, z⁻¹, t.inv_mem hz, ?_⟩
      have h := hc y hy z hz
      calc y⁻¹ * z⁻¹ = (z * y)⁻¹ := by rw [mul_inv_rev]
        _ = (y * z)⁻¹ := by rw [h]
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hy hz

theorem subgroupOf_normal_of_comm {N S : Subgroup G} (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) :
    (S.subgroupOf N).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : G) ∈ S := Subgroup.mem_subgroupOf.1 hn
  have hc : (g : G) * (n : G) = (n : G) * (g : G) := hN _ g.2 _ n.2
  rw [Subgroup.mem_subgroupOf]
  have e : ((g * n * g⁻¹ : ↥N) : G) = (n : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc]
    group
  rw [e]
  exact hn'

def XEquivariant (X : Subgroup G) {J K C D : Subgroup G} [(C.subgroupOf J).Normal]
    [(D.subgroupOf K).Normal] (f : ↥J ⧸ C.subgroupOf J ≃* ↥K ⧸ D.subgroupOf K) : Prop :=
  ∀ x ∈ X, ∀ (j : ↥J) (k : ↥K) (hj : x * (j : G) * x⁻¹ ∈ J) (hk : x * (k : G) * x⁻¹ ∈ K),
    f (j : ↥J ⧸ C.subgroupOf J) = (k : ↥K ⧸ D.subgroupOf K) →
      f ((⟨x * (j : G) * x⁻¹, hj⟩ : ↥J) : ↥J ⧸ C.subgroupOf J) =
        ((⟨x * (k : G) * x⁻¹, hk⟩ : ↥K) : ↥K ⧸ D.subgroupOf K)

theorem XEquivariant.trans {X J K L C D E : Subgroup G} [(C.subgroupOf J).Normal]
    [(D.subgroupOf K).Normal] [(E.subgroupOf L).Normal]
    {f : ↥J ⧸ C.subgroupOf J ≃* ↥K ⧸ D.subgroupOf K}
    {g : ↥K ⧸ D.subgroupOf K ≃* ↥L ⧸ E.subgroupOf L} (hf : XEquivariant X f)
    (hg : XEquivariant X g) (hXK : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) :
    XEquivariant X (f.trans g) := by
  intro x hx j l hj hl h
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (f (j : ↥J ⧸ C.subgroupOf J))
  have hkx : x * (k : G) * x⁻¹ ∈ K := hXK x hx (k : G) k.2
  have h1 : f ((⟨x * (j : G) * x⁻¹, hj⟩ : ↥J) : ↥J ⧸ C.subgroupOf J) =
      ((⟨x * (k : G) * x⁻¹, hkx⟩ : ↥K) : ↥K ⧸ D.subgroupOf K) :=
    hf x hx j k hj hkx (by rw [← hk])
  have h2 : g ((k : ↥K ⧸ D.subgroupOf K)) = (l : ↥L ⧸ E.subgroupOf L) := by
    rw [MulEquiv.trans_apply, ← hk] at h
    exact h
  rw [MulEquiv.trans_apply, h1]
  exact hg x hx k l hkx hl h2

theorem XEquivariant.symm {X J K C D : Subgroup G} [(C.subgroupOf J).Normal]
    [(D.subgroupOf K).Normal]
    {f : ↥J ⧸ C.subgroupOf J ≃* ↥K ⧸ D.subgroupOf K} (hf : XEquivariant X f) :
    XEquivariant X f.symm := by
  intro x hx k j hk hj h
  have h' : f (j : ↥J ⧸ C.subgroupOf J) = (k : ↥K ⧸ D.subgroupOf K) := by
    rw [← h, MulEquiv.apply_symm_apply]
  rw [MulEquiv.symm_apply_eq]
  exact (hf x hx j k hj hk h').symm

end Membership

section SecondIso

theorem secEquiv {X M S N K0 : Subgroup G} (hMN : M ≤ N) (hSN : S ≤ N) (hNMS : N ≤ M ⊔ S)
    (hcN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hK0 : M ⊓ S = K0)
    (hXS : ∀ x ∈ X, ∀ s ∈ S, x * s * x⁻¹ ∈ S) :
    ∃ (_ : (K0.subgroupOf M).Normal) (_ : (S.subgroupOf N).Normal)
      (e : ↥M ⧸ K0.subgroupOf M ≃* ↥N ⧸ S.subgroupOf N), XEquivariant X e := by
  subst hK0
  have hcM : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := fun a ha b hb => hcN a (hMN ha) b (hMN hb)
  haveI hMn : ((M ⊓ S).subgroupOf M).Normal := subgroupOf_normal_of_comm hcM
  haveI hSn : (S.subgroupOf N).Normal := subgroupOf_normal_of_comm hcN
  let φ : ↥M →* ↥N ⧸ S.subgroupOf N :=
    (QuotientGroup.mk' (S.subgroupOf N)).comp (Subgroup.inclusion hMN)
  have hφapply : ∀ m : ↥M, φ m = ((Subgroup.inclusion hMN m : ↥N) : ↥N ⧸ S.subgroupOf N) :=
    fun m => rfl
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, hm, s, hs, hms⟩ :=
      (mem_sup_of_comm (fun a ha b hb => hcN a (hMN ha) b (hSN hb))).1 (hNMS n.2)
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [hφapply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : ((Subgroup.inclusion hMN ⟨m, hm⟩ : ↥N))⁻¹ * n = (⟨s, hSN hs⟩ : ↥N) := by
      apply Subtype.ext
      change m⁻¹ * (n : G) = s
      rw [← hms]
      group
    rw [e]
    exact hs
  have hker : φ.ker = (M ⊓ S).subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, hφapply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨m.2, h⟩, fun h => h.2⟩
  let e₀ := QuotientGroup.quotientKerEquivOfSurjective φ hφs
  let e : ↥M ⧸ (M ⊓ S).subgroupOf M ≃* ↥N ⧸ S.subgroupOf N :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans e₀
  have he : ∀ m : ↥M, e (m : ↥M ⧸ (M ⊓ S).subgroupOf M) = φ m := by
    intro m
    rfl
  have hequiv : XEquivariant X e := by
    intro x hx j k hj hk h
    rw [he, hφapply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    rw [he, hφapply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : (j : G)⁻¹ * (k : G) ∈ S := by
      have h' : (((Subgroup.inclusion hMN j : ↥N))⁻¹ * k : ↥N) ∈ S.subgroupOf N := h
      exact Subgroup.mem_subgroupOf.1 h'
    have h2 := hXS x hx _ h1
    convert h2 using 1
    change (x * (j : G) * x⁻¹)⁻¹ * (x * (k : G) * x⁻¹) = x * ((j : G)⁻¹ * (k : G)) * x⁻¹
    group
  exact ⟨hMn, hSn, e, hequiv⟩

end SecondIso

section Transfer

theorem isIrrPlusIn_of_le {X A A' Y I : Subgroup G}
    (hA' : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a) (hAA' : A ≤ A')
    (hXA : X ≤ Subgroup.normalizer (A : Set G)) (hYA : Y ≤ Subgroup.normalizer (A : Set G))
    (h : IsIrrPlusIn X A Y I) : IsIrrPlusIn X A' Y I := by
  obtain ⟨hIA, hI0, hXI, hcomm, hlt, hirr, hhom⟩ := h
  refine ⟨hIA.trans hAA', hI0, hXI, hcomm, hlt, hirr, ?_⟩
  intro J hJC hJP hXJ hiso
  have hWA : conjClosure I Y ≤ A := conjClosure_le fun y hy z hz =>
    (Subgroup.mem_normalizer_iff.1 (hYA hy) z).1 (hIA hz)
  have hWA' : conjClosure I Y ≤ A' := hWA.trans hAA'
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hCdef
  set Ca : Subgroup G := A ⊓ C with hCa
  set Ca' : Subgroup G := A' ⊓ C with hCa'
  have hCaCa' : Ca ≤ Ca' := inf_le_inf_right C hAA'
  have hCa'A' : Ca' ≤ A' := inf_le_left
  have hCa'C : Ca' ≤ C := inf_le_right
  have hCaA : Ca ≤ A := inf_le_left
  have hCaJ : Ca ≤ J := hCaCa'.trans hJC
  have hXC : ∀ x ∈ X, ∀ c ∈ C, x * c * x⁻¹ = c := by
    intro x hx c hc
    have h1 : x * c = c * x := (Subgroup.mem_centralizer_iff.1 hc) x hx
    rw [h1]
    group
  have hXCa' : ∀ x ∈ X, ∀ s ∈ Ca', x * s * x⁻¹ ∈ Ca' := by
    intro x hx s hs
    rw [hXC x hx s (hCa'C hs)]
    exact hs
  have hJdec : ∀ x ∈ J, ∃ c ∈ conjClosure I Y, ∃ d ∈ Ca', c * d = x := by
    intro x hx
    refine (mem_sup_of_comm ?_).1 (hJP hx)
    intro a ha b hb
    exact hA' a (hWA' ha) b (hCa'A' hb)
  have hJA' : J ≤ A' := by
    intro x hx
    obtain ⟨c, hc, d, hd, rfl⟩ := hJdec x hx
    exact A'.mul_mem (hWA' hc) (hCa'A' hd)
  have hXJA : X ≤ Subgroup.normalizer ((J ⊓ A : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hJy := Subgroup.mem_normalizer_iff.1 (hXJ hx) y
    have hAy := Subgroup.mem_normalizer_iff.1 (hXA hx) y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hJy, hAy]
  have hNMS1 : J ≤ (J ⊓ A) ⊔ Ca' := by
    intro x hx
    obtain ⟨c, hc, d, hd, rfl⟩ := hJdec x hx
    have hcJ : c ∈ J := by
      have := J.mul_mem hx (J.inv_mem (hJC hd))
      simpa using this
    exact Subgroup.mul_mem_sup ⟨hcJ, hWA hc⟩ hd
  have hK01 : (J ⊓ A) ⊓ Ca' = Ca := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.2, hCa'C hx.2⟩
    · intro hx
      exact ⟨⟨hCaJ hx, hCaA hx⟩, hCaCa' hx⟩
  have hcJ' : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := fun a ha b hb =>
    hA' a (hJA' ha) b (hJA' hb)
  obtain ⟨n₁, n₂, e₁, he₁⟩ :=
    secEquiv (X := X) (M := J ⊓ A) (S := Ca') (N := J) (K0 := Ca) inf_le_left hJC hNMS1
      hcJ' hK01 hXCa'
  have hI'A' : I ⊔ Ca' ≤ A' := sup_le (hIA.trans hAA') hCa'A'
  have hcI' : ∀ a ∈ I ⊔ Ca', ∀ b ∈ I ⊔ Ca', a * b = b * a :=
    fun a ha b hb => hA' a (hI'A' ha) b (hI'A' hb)
  have hK02 : (I ⊔ Ca) ⊓ Ca' = Ca := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, c, hc, rfl⟩ := (mem_sup_of_comm (fun a ha b hb =>
        hA' a (hIA.trans hAA' ha) b ((hCaA.trans hAA') hb))).1 hx.1
      have hiCa' : i ∈ Ca' := by
        have := Ca'.mul_mem hx.2 (Ca'.inv_mem (hCaCa' hc))
        simpa using this
      exact Ca.mul_mem ⟨hIA hi, hCa'C hiCa'⟩ hc
    · intro hx
      exact ⟨(le_sup_right : Ca ≤ I ⊔ Ca) hx, hCaCa' hx⟩
  have hNMS2 : I ⊔ Ca' ≤ (I ⊔ Ca) ⊔ Ca' := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  obtain ⟨n₃, n₄, e₂, he₂⟩ :=
    secEquiv (X := X) (M := I ⊔ Ca) (S := Ca') (N := I ⊔ Ca') (K0 := Ca)
      (sup_le_sup_left hCaCa' I) le_sup_right hNMS2 hcI' hK02 hXCa'
  obtain ⟨nJ, nK, e, he⟩ := hiso
  have heJ : XEquivariant X e := he
  have hXK1 : ∀ x ∈ X, ∀ k ∈ J, x * k * x⁻¹ ∈ J := fun x hx k hk =>
    (Subgroup.mem_normalizer_iff.1 (hXJ hx) k).1 hk
  have hXK2 : ∀ x ∈ X, ∀ k ∈ I ⊔ Ca', x * k * x⁻¹ ∈ I ⊔ Ca' := by
    intro x hx k hk
    obtain ⟨i, hi, c, hc, rfl⟩ := (mem_sup_of_comm (fun a ha b hb =>
      hA' a (hIA.trans hAA' ha) b (hCa'A' hb))).1 hk
    have e' : x * (i * c) * x⁻¹ = (x * i * x⁻¹) * (x * c * x⁻¹) := by group
    rw [e']
    exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.1 (hXI hx) i).1 hi)
      (hXCa' x hx c hc)
  have hfinal : XEquivariant X (e₁.trans (e.trans e₂.symm)) :=
    XEquivariant.trans he₁ (XEquivariant.trans heJ (XEquivariant.symm he₂) hXK2) hXK1
  have hIsoJA : IsXSectionIso X Ca (J ⊓ A) (I ⊔ Ca) := by
    unfold IsXSectionIso
    exact ⟨n₁, n₃, e₁.trans (e.trans e₂.symm), hfinal⟩
  have hXJA : X ≤ Subgroup.normalizer ((J ⊓ A : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hJy := Subgroup.mem_normalizer_iff.1 (hXJ hx) y
    have hAy := Subgroup.mem_normalizer_iff.1 (hXA hx) y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hJy, hAy]
  have hJA_le : J ⊓ A ≤ conjClosure I Y ⊔ Ca := by
    intro x hx
    obtain ⟨c, hc, d, hd, rfl⟩ := hJdec x hx.1
    have hdA : d ∈ A := by
      have := A.mul_mem (A.inv_mem (hWA hc)) hx.2
      simpa using this
    exact Subgroup.mul_mem_sup hc ⟨hdA, hCa'C hd⟩
  have hsubJA : J ⊓ A ≤ I ⊔ Ca := hhom (J ⊓ A) (le_inf hCaJ hCaA) hJA_le hXJA hIsoJA
  intro x hx
  obtain ⟨c, hc, d, hd, rfl⟩ := hJdec x hx
  have hcJ : c ∈ J := by
    have := J.mul_mem hx (J.inv_mem (hJC hd))
    simpa using this
  have hcJA : c ∈ J ⊓ A := ⟨hcJ, hWA hc⟩
  exact (I ⊔ Ca').mul_mem (sup_le_sup_left hCaCa' I (hsubJA hcJA))
    ((le_sup_right : Ca' ≤ I ⊔ Ca') hd)

end Transfer

section Reduced

theorem isPrimeReduced_subgroupOf_of_isTwoReducedIn {H V : Subgroup G}
    (hV : CFSG.Quasithin.IsTwoReducedIn H V) : IsPrimeReduced 2 (V.subgroupOf H) := by
  obtain ⟨hVH, hHN, hV2, hred⟩ := hV
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV2.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hnorm : (V.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg := (Subgroup.mem_normalizer_iff.1 (hHN g.2) (n : G)).1 hn
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hg⟩
  refine (CFSG.Quasithin.isPrimeReduced_iff_forall 2).2 ⟨hnorm, ?_, ?_⟩
  · refine (CFSG.Quasithin.BlueprintB2.isElementaryAbelian_iff).2 ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
    · exact Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hV2.2 _ (Subgroup.mem_subgroupOf.1 ha))
  · intro D hD hDpow
    have hD'H : D.map H.subtype ≤ H := Subgroup.map_subtype_le D
    have hkey : ∀ g : ↥H, ∀ x ∈ D.map H.subtype, (g : G) * x * (g : G)⁻¹ ∈ D.map H.subtype := by
      intro g x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      exact Subgroup.mem_map.2 ⟨g * y * g⁻¹, hD.conj_mem y hy g, by simp⟩
    have hHD' : H ≤ Subgroup.normalizer ((D.map H.subtype : Subgroup G) : Set G) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact hkey ⟨h, hh⟩ x
      · intro hx
        have h3 := hkey ⟨h, hh⟩⁻¹ _ hx
        have e : ((⟨h, hh⟩⁻¹ : ↥H) : G) * (h * x * h⁻¹) * ((⟨h, hh⟩⁻¹ : ↥H) : G)⁻¹ = x := by
          change h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x
          group
        rw [e] at h3
        exact h3
    have hpow' : ∀ d ∈ D.map H.subtype, ∃ k : ℕ,
        d ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G) := by
      intro d hd
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hd
      obtain ⟨k, hk⟩ := hDpow y hy
      refine ⟨k, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 := Subgroup.mem_centralizer_iff.1 hk ⟨v, hVH hv⟩ (Subgroup.mem_subgroupOf.2 hv)
      have h2 := congrArg Subtype.val h1
      simpa [Subgroup.coe_pow] using h2
    have hD'C := hred (D.map H.subtype) hD'H hHD' hpow'
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : (v : G) ∈ V := Subgroup.mem_subgroupOf.1 hv
    have hc : (v : G) * (y : G) = (y : G) * (v : G) :=
      Subgroup.mem_centralizer_iff.1 (hD'C (Subgroup.mem_map.2 ⟨y, hy, rfl⟩)) v hv'
    exact Subtype.ext hc

theorem le_reducedAggregate_of_isTwoReducedIn {H V : Subgroup G}
    (hV : CFSG.Quasithin.IsTwoReducedIn H V) : V ≤ reducedAggregate H := by
  have hmem : V.subgroupOf H ∈ primeReducedFamily ↥H 2 :=
    isPrimeReduced_subgroupOf_of_isTwoReducedIn hV
  have hle : V.subgroupOf H ≤ primeReducedAggregate ↥H 2 := le_sSup hmem
  intro x hx
  have hxH : (⟨x, hV.1 hx⟩ : ↥H) ∈ V.subgroupOf H := Subgroup.mem_subgroupOf.2 hx
  exact ⟨_, hle hxH, rfl⟩

end Reduced

end IDIrr

end CFSG.Quasithin.H13.C1294
