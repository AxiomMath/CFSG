module

public import CFSG.Quasithin.Background.RonanE111Quot
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch11SecBNPStar

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB

variable {G : Type} [Group G]

theorem isSubnormal_map_inf_normal {Y N : Subgroup G} [N.Normal] (hNY : N ≤ Y)
    {H' : Subgroup ↥Y} (h : H'.IsSubnormal) : (H'.map Y.subtype ⊓ N).IsSubnormal := by
  induction h with
  | top =>
    have : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [this, inf_eq_right.mpr hNY]
    exact Subgroup.Normal.isSubnormal inferInstance
  | step A B hAB hB hN ih =>
    refine Subgroup.IsSubnormal.step _ _ (inf_le_inf_right _ (Subgroup.map_mono hAB)) ih ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_inf_right _ (Subgroup.map_mono hAB))]
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAB] at hN
    have key : ∀ b ∈ B.map Y.subtype ⊓ N, ∀ a ∈ A.map Y.subtype ⊓ N,
        b * a * b⁻¹ ∈ A.map Y.subtype ⊓ N := by
      rintro _ ⟨⟨b', hb'B, rfl⟩, hbN⟩ _ ⟨⟨a', ha'A, rfl⟩, haN⟩
      have hb'n := (Subgroup.mem_normalizer_iff.mp (hN hb'B) a').mp ha'A
      refine ⟨⟨b' * a' * b'⁻¹, hb'n, by simp⟩, ?_⟩
      have := ‹N.Normal›.conj_mem _ haN (b' : G)
      simpa using this
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => key b hb a ha, fun ha => ?_⟩
    have hbinv : b⁻¹ ∈ B.map Y.subtype ⊓ N := inv_mem hb
    have := key b⁻¹ hbinv _ ha
    simpa [mul_assoc] using this


theorem mem_normalizer_map_subtype_iff {Y : Subgroup G} (H : Subgroup ↥Y) (g : ↥Y) :
    g ∈ Subgroup.normalizer (H : Set ↥Y) ↔
      (g : G) ∈ Subgroup.normalizer ((H.map Y.subtype : Subgroup G) : Set G) := by
  have h1 : H.map Y.subtype ≤ Y := Subgroup.map_subtype_le H
  have h2 := Subgroup.subgroupOf_normalizer_eq h1
  have h4 : (H.map Y.subtype).subgroupOf Y = H :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective H
  rw [h4] at h2
  have h3 : g ∈ (Subgroup.normalizer ((H.map Y.subtype : Subgroup G) : Set G)).subgroupOf Y ↔
      g ∈ Subgroup.normalizer (H : Set ↥Y) := by rw [h2]
  exact (Subgroup.mem_subgroupOf.symm.trans h3).symm

theorem HypT.of_overgroup [Finite G] {n : ℕ} {T N Y : Subgroup G} [N.Normal] (hNY : N ≤ Y)
    (hTY : T ≤ Y) (hY2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ N)
    (h : HypT n G T) : HypT n ↥Y (T.subgroupOf Y) := by
  intro M' K' _ hKM hMsn hTK hsimple hnab
  set ι : ↥Y →* G := Y.subtype with hι
  have hιinj : Function.Injective ι := Y.subtype_injective
  set M₀ : Subgroup G := M'.map ι with hM₀
  set K₀ : Subgroup G := K'.map ι with hK₀
  set M : Subgroup G := M₀ ⊓ N with hM
  set K : Subgroup G := K₀ ⊓ N with hK
  have hK₀M₀ : K₀ ≤ M₀ := Subgroup.map_mono hKM
  have hKM' : K ≤ M := inf_le_inf_right _ hK₀M₀
  have hMM₀ : M ≤ M₀ := inf_le_left
  have hMN : M ≤ N := inf_le_right
  have hKnorm : M' ≤ Subgroup.normalizer (K' : Set ↥Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp ‹_›
  have hM₀K₀ : M₀ ≤ Subgroup.normalizer (K₀ : Set G) :=
    (Subgroup.map_mono hKnorm).trans (Subgroup.le_normalizer_map ι)
  have hTK₀ : T ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro t ht
    have h1 := hTK (Subgroup.mem_subgroupOf.mpr ht : (⟨t, hTY ht⟩ : ↥Y) ∈ T.subgroupOf Y)
    exact Subgroup.le_normalizer_map ι (Subgroup.mem_map_of_mem ι h1)
  have hNnorm : Subgroup.normalizer (N : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hKnormal : (K.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKM']
    intro m hm
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hM₀K₀ hm.1, hNnorm ▸ Subgroup.mem_top m⟩
  have hMsub : M.IsSubnormal := isSubnormal_map_inf_normal hNY hMsn
  have hTKn : T ≤ Subgroup.normalizer (K : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTK₀ ht, hNnorm ▸ Subgroup.mem_top t⟩
  have hMn : ∀ x ∈ M₀, ∀ m ∈ M, x * m * x⁻¹ ∈ M := fun x hx m hm =>
    ⟨M₀.mul_mem (M₀.mul_mem hx hm.1) (M₀.inv_mem hx), by
      simpa using ‹N.Normal›.conj_mem _ hm.2 x⟩
  have hMY : ∀ x ∈ M₀, x ∈ Y := fun x hx => Subgroup.map_subtype_le M' hx
  let j : ↥M →* ↥M' :=
    { toFun := fun m =>
        ⟨⟨(m : G), hMY _ (hMM₀ m.2)⟩, by
          obtain ⟨m', hm', hm'e⟩ := hMM₀ m.2
          have : m' = ⟨(m : G), hMY _ (hMM₀ m.2)⟩ := Subtype.ext hm'e
          rw [← this]; exact hm'⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : ∀ m : ↥M, (((j m : ↥M') : ↥Y) : G) = (m : G) := fun m => rfl
  set ψ : ↥M →* ↥M' ⧸ K'.subgroupOf M' := (QuotientGroup.mk' (K'.subgroupOf M')).comp j with hψ
  have hker : ψ.ker = K.subgroupOf M := by
    ext m
    simp only [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hmK : ((j m : ↥M') : ↥Y) ∈ K' ↔ (m : G) ∈ K₀ := by
      rw [hK₀]
      constructor
      · intro hh
        exact ⟨_, hh, rfl⟩
      · rintro ⟨y, hy, hye⟩
        have : y = ((j m : ↥M') : ↥Y) := hιinj hye
        rwa [← this]
    rw [hmK]
    exact ⟨fun hh => ⟨hh, hMN m.2⟩, fun hh => hh.1⟩
  have hrangeN : (ψ.range).Normal := by
    refine ⟨fun r hr q => ?_⟩
    obtain ⟨m, rfl⟩ := hr
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective q
    have hx : ((x' : ↥Y) : G) ∈ M₀ := ⟨(x' : ↥Y), x'.2, rfl⟩
    refine ⟨⟨((x' : ↥Y) : G) * (m : G) * ((x' : ↥Y) : G)⁻¹, hMn _ hx m m.2⟩, ?_⟩
    have : j ⟨((x' : ↥Y) : G) * (m : G) * ((x' : ↥Y) : G)⁻¹, hMn _ hx m m.2⟩ = x' * j m * x'⁻¹ :=
      Subtype.ext (Subtype.ext rfl)
    simp only [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, this, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψs : Function.Surjective ψ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.range with hbot | htop
    · exfalso
      have h2q : IsPGroup 2 (↥M' ⧸ K'.subgroupOf M') := by
        intro q
        obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨e, he⟩ := hY2 ((x' : ↥Y) : G) (x' : ↥Y).2
        have hxe : ((x' : ↥Y) : G) ^ 2 ^ e ∈ M :=
          ⟨M₀.pow_mem ⟨(x' : ↥Y), x'.2, rfl⟩ _, he⟩
        have hψ1 : ψ ⟨_, hxe⟩ = 1 := by
          have : ψ ⟨_, hxe⟩ ∈ ψ.range := ⟨_, rfl⟩
          rwa [hbot, Subgroup.mem_bot] at this
        refine ⟨e, ?_⟩
        have hjx : j ⟨_, hxe⟩ = x' ^ 2 ^ e := Subtype.ext (Subtype.ext (by rw [hj]; simp))
        rw [← QuotientGroup.mk_pow, ← hjx]
        simpa [hψ] using hψ1
      have := h2q.isNilpotent
      exact not_nonabelian_of_isSolvable inferInstance hnab
    · exact MonoidHom.range_eq_top.mp htop
  have hdecomp : ∀ x ∈ M₀, ∃ m ∈ M, ∃ k ∈ K₀, x = m * k := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨m, hm⟩ := hψs (QuotientGroup.mk ⟨x', hx'⟩)
    have hm' : ((j m : ↥M') : ↥Y)⁻¹ * x' ∈ K' := by
      have := QuotientGroup.eq.mp hm
      exact Subgroup.mem_subgroupOf.mp this
    refine ⟨(m : G), m.2, ι (((j m : ↥M') : ↥Y)⁻¹ * x'), ⟨_, hm', rfl⟩, ?_⟩
    have : ι (((j m : ↥M') : ↥Y)⁻¹ * x') = (m : G)⁻¹ * ι x' := by
      simp only [map_mul, map_inv]
      rfl
    rw [this]
    group
  obtain ⟨e, he⟩ : ∃ e : (↥M ⧸ K.subgroupOf M) ≃* (↥M' ⧸ K'.subgroupOf M'),
      ∀ m : ↥M, e (QuotientGroup.mk m) = QuotientGroup.mk (j m) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs), fun m => rfl⟩
  have hsM : IsSimpleGroup (↥M ⧸ K.subgroupOf M) := (MulEquiv.isSimpleGroup_congr e).mpr hsimple
  have hnabM := quotNonabelian e hnab
  have hb := h M K hKM' hMsub hTKn hsM hnabM
  have hSM : (T ⊓ Subgroup.normalizer (M : Set G) ⊓ Subgroup.normalizer (K : Set G)) ≤
      Subgroup.normalizer (M : Set G) := fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2
  have hSM' : (T.subgroupOf Y ⊓ Subgroup.normalizer (M' : Set ↥Y) ⊓
      Subgroup.normalizer (K' : Set ↥Y)) ≤ Subgroup.normalizer (M' : Set ↥Y) :=
    fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2
  have hN1 : ∀ s ∈ T, s ∈ Subgroup.normalizer (M : Set G) →
      s ∈ Subgroup.normalizer (M₀ : Set G) := by
    intro s hsT hsM
    have key : ∀ t ∈ T, t ∈ Subgroup.normalizer (M : Set G) →
        ∀ x ∈ M₀, t * x * t⁻¹ ∈ M₀ := by
      intro t htT htM x hx
      obtain ⟨m, hm, k, hk, rfl⟩ := hdecomp x hx
      have h1 : t * m * t⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp htM m).mp hm
      have h2 : t * k * t⁻¹ ∈ K₀ := (Subgroup.mem_normalizer_iff.mp (hTK₀ htT) k).mp hk
      have : t * (m * k) * t⁻¹ = (t * m * t⁻¹) * (t * k * t⁻¹) := by group
      rw [this]
      exact M₀.mul_mem (hMM₀ h1) (hK₀M₀ h2)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key s hsT hsM x hx, fun hx => ?_⟩
    have := key s⁻¹ (T.inv_mem hsT) (inv_mem hsM) _ hx
    simpa [mul_assoc] using this
  have hN2 : ∀ g' : ↥Y, g' ∈ Subgroup.normalizer (M' : Set ↥Y) →
      (g' : G) ∈ Subgroup.normalizer (M : Set G) := fun g' hg' =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(mem_normalizer_map_subtype_iff M' g').mp hg', hNnorm ▸ Subgroup.mem_top _⟩
  have hmemK' : ∀ z : ↥Y, ι z ∈ K₀ → z ∈ K' := fun z ⟨w, hw, hwz⟩ => by
    have := hιinj hwz
    rw [← this]
    exact hw
  have hNorm_K₀ : ∀ x ∈ M₀, ∀ k ∈ K₀, x * k * x⁻¹ ∈ K₀ := fun x hx k hk =>
    (Subgroup.mem_normalizer_iff.mp (hM₀K₀ hx) k).mp hk
  have hInd1 : ∀ (g : G) (hgY : g ∈ Y), g ∈ Subgroup.normalizer (M₀ : Set G) →
      g ∈ Subgroup.normalizer (K₀ : Set G) → ∀ α, Induces M K g α →
        Induces M' K' ⟨g, hgY⟩ (MulAut.congr e α) := by
    intro g hgY hgM₀ hgK₀ α hα x'
    have hxM₀ : ((x' : ↥Y) : G) ∈ M₀ := ⟨(x' : ↥Y), x'.2, rfl⟩
    obtain ⟨m, hm⟩ := hψs (QuotientGroup.mk x')
    obtain ⟨m_y, hm_y1, hm_y2⟩ := hα m
    have hgx : g * ((x' : ↥Y) : G) * g⁻¹ ∈ M₀ := (Subgroup.mem_normalizer_iff.mp hgM₀ _).mp hxM₀
    obtain ⟨y'', hy''M', hy''⟩ := hgx
    refine ⟨⟨y'', hy''M'⟩, Subtype.ext ?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hy''
    · have hex : (QuotientGroup.mk x' : ↥M' ⧸ K'.subgroupOf M') = e (QuotientGroup.mk m) := by
        rw [he]
        exact hm.symm
      rw [hex, quotCongrApply, hm_y2, he]
      refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (hmemK' _ ?_))
      have hm' : ((j m : ↥M') : ↥Y)⁻¹ * (x' : ↥Y) ∈ K' := by
        have := QuotientGroup.eq.mp hm
        exact Subgroup.mem_subgroupOf.mp this
      have hK1 : (m : G)⁻¹ * ((x' : ↥Y) : G) ∈ K₀ :=
        ⟨_, hm', by simp only [hι, map_mul, map_inv, Subgroup.coe_subtype]; rw [hj]⟩
      have hK2 := (Subgroup.mem_normalizer_iff.mp hgK₀ _).mp hK1
      have hcalc : ι ((((j m_y)⁻¹ * (⟨y'', hy''M'⟩ : ↥M') : ↥M') : ↥Y)) =
          g * ((m : G)⁻¹ * ((x' : ↥Y) : G)) * g⁻¹ := by
        simp only [hι, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
        rw [hj, hm_y1]
        have : (y'' : G) = g * ((x' : ↥Y) : G) * g⁻¹ := hy''
        rw [this]
        group
      rw [hcalc]
      exact hK2
  have hInd2 : ∀ (m' : ↥M') (s' : ↥Y), s' ∈ T.subgroupOf Y ⊓ Subgroup.normalizer (M' : Set ↥Y) ⊓
        Subgroup.normalizer (K' : Set ↥Y) → ∃ g ∈ M ⊔ (T ⊓ Subgroup.normalizer (M : Set G) ⊓
          Subgroup.normalizer (K : Set G)), ∀ α', Induces M' K' ((m' : ↥Y) * s') α' →
            Induces M K g ((MulAut.congr e).symm α') := by
    intro m' s' hs'
    obtain ⟨⟨hs'T, hs'M⟩, hs'K⟩ := Subgroup.mem_inf.mp hs' |>.imp_left Subgroup.mem_inf.mp
    have hsT : (s' : G) ∈ T := Subgroup.mem_subgroupOf.mp hs'T
    have hsM : (s' : G) ∈ Subgroup.normalizer (M : Set G) := hN2 s' hs'M
    obtain ⟨x, hx, k, hk, hxk⟩ := hdecomp ((m' : ↥Y) : G) ⟨(m' : ↥Y), m'.2, rfl⟩
    have hsS : (s' : G) ∈ T ⊓ Subgroup.normalizer (M : Set G) ⊓ Subgroup.normalizer (K : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hsT, hsM⟩, hTKn hsT⟩
    refine ⟨x * (s' : G), Subgroup.mul_mem_sup hx hsS, fun α' hα' y => ?_⟩
    have hz : (s' : G) * (y : G) * (s' : G)⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hsM (y : G)).mp y.2
    have hgy : (x * (s' : G)) * (y : G) * (x * (s' : G))⁻¹ ∈ M := by
      have : (x * (s' : G)) * (y : G) * (x * (s' : G))⁻¹ =
          x * ((s' : G) * (y : G) * (s' : G)⁻¹) * x⁻¹ := by group
      rw [this]
      exact M.mul_mem (M.mul_mem hx hz) (M.inv_mem hx)
    refine ⟨⟨(x * (s' : G)) * (y : G) * (x * (s' : G))⁻¹, hgy⟩, rfl, ?_⟩
    apply e.injective
    rw [quotCongrSymmApply, he, he]
    obtain ⟨w, hw1, hw2⟩ := hα' (j y)
    rw [hw2]
    refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (hmemK' _ ?_))
    have hzM : (s' : G) * (y : G) * (s' : G)⁻¹ ∈ M₀ := hMM₀ hz
    have hk1 : ((s' : G) * (y : G) * (s' : G)⁻¹)⁻¹ * k⁻¹ * ((s' : G) * (y : G) * (s' : G)⁻¹) ∈ K₀ := by
      have := hNorm_K₀ _ (M₀.inv_mem hzM) k⁻¹ (K₀.inv_mem hk)
      simpa using this
    have hk2 : k * (((s' : G) * (y : G) * (s' : G)⁻¹)⁻¹ * k⁻¹ * ((s' : G) * (y : G) * (s' : G)⁻¹)) ∈ K₀ :=
      K₀.mul_mem hk hk1
    have hk3 := hNorm_K₀ x (hMM₀ hx) _ hk2
    have hw1' : ((w : ↥Y) : G) = (x * k * (s' : G)) * (y : G) * (x * k * (s' : G))⁻¹ := by
      have := congrArg (fun z : ↥Y => (z : G)) hw1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      have hmm : (((m' : ↥M') : ↥Y) : G) = x * k := hxk
      rw [hmm] at this
      simpa [hj] using this
    have hfin : ι ((((w⁻¹ * j ⟨(x * (s' : G)) * (y : G) * (x * (s' : G))⁻¹, hgy⟩ : ↥M') : ↥Y))) =
        x * (k * (((s' : G) * (y : G) * (s' : G)⁻¹)⁻¹ * k⁻¹ *
          ((s' : G) * (y : G) * (s' : G)⁻¹))) * x⁻¹ := by
      simp only [hι, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
      rw [hw1', hj]
      group
    rw [hfin]
    exact hk3
  have hgY : ∀ m ∈ M, ∀ s ∈ T, m * s ∈ Y := fun m hm s hs =>
    Y.mul_mem (hMY _ (hMM₀ hm)) (hTY hs)
  have h1 : ∀ g ∈ M ⊔ (T ⊓ Subgroup.normalizer (M : Set G) ⊓ Subgroup.normalizer (K : Set G)),
      ∃ g' ∈ M' ⊔ (T.subgroupOf Y ⊓ Subgroup.normalizer (M' : Set ↥Y) ⊓
        Subgroup.normalizer (K' : Set ↥Y)),
        ∀ α, Induces M K g α → Induces M' K' g' (MulAut.congr e α) := by
    intro g hg
    obtain ⟨m, hm, s, hs, rfl⟩ := quotSupMul hSM hg
    obtain ⟨⟨hsT, hsM⟩, hsK⟩ := Subgroup.mem_inf.mp hs |>.imp_left Subgroup.mem_inf.mp
    have hsMY : (⟨s, hTY hsT⟩ : ↥Y) ∈ Subgroup.normalizer (M' : Set ↥Y) :=
      (mem_normalizer_map_subtype_iff M' _).mpr (hN1 s hsT hsM)
    have hsKY : (⟨s, hTY hsT⟩ : ↥Y) ∈ Subgroup.normalizer (K' : Set ↥Y) :=
      hTK (Subgroup.mem_subgroupOf.mpr hsT)
    refine ⟨⟨m * s, hgY m hm s hsT⟩, ?_, fun α hα => ?_⟩
    · have : (⟨m * s, hgY m hm s hsT⟩ : ↥Y) =
          ((j ⟨m, hm⟩ : ↥M') : ↥Y) * ⟨s, hTY hsT⟩ := Subtype.ext rfl
      rw [this]
      exact Subgroup.mul_mem_sup (j ⟨m, hm⟩).2
        (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hsT, hsMY⟩, hsKY⟩)
    · refine hInd1 (m * s) (hgY m hm s hsT) ?_ ?_ α hα
      · exact mul_mem (Subgroup.le_normalizer (hMM₀ hm)) (hN1 s hsT hsM)
      · exact mul_mem (hM₀K₀ (hMM₀ hm)) (hTK₀ hsT)
  have h2 : ∀ g' ∈ M' ⊔ (T.subgroupOf Y ⊓ Subgroup.normalizer (M' : Set ↥Y) ⊓
        Subgroup.normalizer (K' : Set ↥Y)),
      ∃ g ∈ M ⊔ (T ⊓ Subgroup.normalizer (M : Set G) ⊓ Subgroup.normalizer (K : Set G)),
        ∀ α', Induces M' K' g' α' → Induces M K g ((MulAut.congr e).symm α') := by
    intro g' hg'
    obtain ⟨m', hm', s', hs', rfl⟩ := quotSupMul hSM' hg'
    exact hInd2 ⟨m', hm'⟩ s' hs'
  have hfM : Finite (MulAut (↥M ⧸ K.subgroupOf M)) := quotFiniteMulAut _
  have hfM' : Finite (MulAut (↥M' ⧸ K'.subgroupOf M')) := quotFiniteMulAut _
  rw [innAutInduced_eq, nParam_closure_indSet_congr e h1 h2]
  exact hb


theorem HypT.sup [Finite G] {n : ℕ} {T N : Subgroup G} [N.Normal] (hT : IsPGroup 2 T)
    (h : HypT n G T) : HypT n ↥(N ⊔ T) (T.subgroupOf (N ⊔ T)) :=
  HypT.of_overgroup le_sup_left le_sup_right (pow_mem_of_mem_sup_normal hT) h

end CFSG.Quasithin.RonanE111
