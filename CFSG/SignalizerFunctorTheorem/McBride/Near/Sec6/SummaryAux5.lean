module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.SummaryAux6
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.SummaryAux7
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.SummaryAux2

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S34

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {h : Counterexample p A θ} {E : Subgroup G} {f : G}

theorem Data.exists_plane
    (d : Data h E f) :
    ∃ e ∈ A, e ∉ E ⊔ Subgroup.zpowers f ∧
      (Subgroup.zpowers f ⊔ Subgroup.zpowers e) ∈ rSet p A θ ∧
      kOf (thetaOf θ (Subgroup.zpowers f ⊔ Subgroup.zpowers e)) ≤ kOf (θ f) := by
  obtain ⟨e, he, hen⟩ := d.exists_mem_sdiff
  exact ⟨e, he, hen, (d.plane_mem_rSetN_two he hen).1, (d.kOf_plane he hen).le.trans inf_le_left⟩

theorem Data.sol_eq_bot_of_le
    (d : Data h E f) {X : Subgroup G} (hX : X ∈ assoc p A θ)
    (hKX : kOf (θ f) ≤ X) : sol X = ⊥ := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨e, he, hen, hB, hBK⟩ := d.exists_plane
  have hAS : Admits A (sol X) := hX.1.trans (Nonsolv.SolQuot.normalizer_le_nrm_sol X)
  have hS : sol X ∈ assoc p A θ := mem_assoc_of_le hθ.prime hX (sol_le X) hAS
  exact h.lemma618 hB hS (isSolvable_sol X)
    ((hBK.trans hKX).trans (Nonsolv.SolQuot.le_nrm_sol X))

theorem Data.inf_centralizer_kOf_eq_bot
    (d : Data h E f) :
    θ f ⊓ Subgroup.centralizer (kOf (θ f) : Set G) = ⊥ :=
  centralizer_kOf_eq_bot d.sol_eq_bot

theorem Data.admits_kOf (d : Data h E f) : Admits A (kOf (θ f)) :=
  (h.hyp.nearFunctor.isFunctor.normalized f d.mem d.ne_one).trans
    (Thm211.normalizer_le_normalizer_kOf (θ f))

theorem Data.cenIn_eq_bot
    (d : Data h E f) {X : Subgroup G} (hX : X ∈ assoc p A θ) :
    X ⊓ Subgroup.centralizer (kOf (θ f) : Set G) = ⊥ := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨e, he, hen, hB, hBK⟩ := d.exists_plane
  have hAZ : Admits A (X ⊓ Subgroup.centralizer (kOf (θ f) : Set G)) :=
    Admits.inf hX.1 (Sec6S33.admits_centralizer d.admits_kOf)
  have hZ : X ⊓ Subgroup.centralizer (kOf (θ f) : Set G) ∈ assoc p A θ :=
    mem_assoc_of_le hθ.prime hX inf_le_left hAZ
  have hfix : X ⊓ Subgroup.centralizer (kOf (θ f) : Set G) ⊓ Subgroup.centralizer {f} = ⊥ := by
    rw [eq_bot_iff, ← d.inf_centralizer_kOf_eq_bot]
    rintro x ⟨⟨hxX, hxK⟩, hxf⟩
    exact ⟨hZ.2.2.1 f d.mem d.ne_one ⟨⟨hxX, hxK⟩, hxf⟩, hxK⟩
  have := Fact.mk hθ.prime
  have hord : orderOf f = p := orderOf_eq_prime (hθ.elemAbelian.2 f d.mem) d.ne_one
  have hfn : f ∈ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (kOf (θ f) : Set G) :
      Subgroup G) : Set G) := hAZ d.mem
  have hnil := Thompson.fpf_nilpotent hθ.prime hord hfn hfix
  have hsolv : Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (kOf (θ f) : Set G)) := inferInstance
  refine h.lemma618 hB hZ hsolv ?_
  refine fun k hk => ?_
  have hkc : k ∈ Subgroup.centralizer ((X ⊓ Subgroup.centralizer (kOf (θ f) : Set G) :
      Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 k (hBK hk)).symm
  exact Subgroup.centralizer_le_normalizer _ hkc

theorem Data.eq_bot_or_eq_kOf
    (d : Data h E f) {N : Subgroup G} (hNK : N ≤ kOf (θ f))
    (hNn : (N.subgroupOf (kOf (θ f))).Normal) (hNA : Admits A N) :
    N = ⊥ ∨ N = kOf (θ f) := by
  by_cases hN1 : N = ⊥
  · exact Or.inl hN1
  right
  have hD := d.isDirectProduct
  have hss : IsSemisimple (kOf (θ f)) := isSemisimple_kOf d.sol_eq_bot
  have hLn : ∀ L ∈ lcal (θ f), ∀ t ∈ L, ∀ k ∈ kOf (θ f), k * t * k⁻¹ ∈ L := by
    intro L hL t ht k hk
    have hL' : L ∈ lcal (kOf (θ f)) := d.lcal_kOf ▸ hL
    rw [hss.lcal_eq] at hL'
    exact (Subgroup.normal_subgroupOf_iff hL'.1).mp hL'.2.1 t k ht hk
  have hNmem : ∀ n ∈ N, ∀ k ∈ kOf (θ f), k * n * k⁻¹ ∈ N :=
    fun n hn k hk => (Subgroup.normal_subgroupOf_iff hNK).mp hNn n k hn hk
  obtain ⟨L₀, hL₀⟩ := d.lcal_nonempty
  have hL₀K : L₀ ≤ kOf (θ f) := lcal_le (d.lcal_kOf ▸ hL₀ : L₀ ∈ lcal (kOf (θ f)))
  by_cases hcase : L₀ ≤ N
  · refine le_antisymm hNK ?_
    rw [← hD.sSup_eq]
    refine sSup_le fun L hL => ?_
    obtain ⟨a, ha, rfl⟩ := d.exists_conj_A hL₀ hL
    have hmap : N.map (MulAut.conj a).toMonoidHom = N :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNA ha)
    rw [← hmap]
    exact Subgroup.map_mono hcase
  · exfalso
    have : IsSimpleGroup ↥L₀ := (mem_lcal_iff.mp hL₀).2.2.1
    have hDn : ((L₀ ⊓ N).subgroupOf L₀).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_left]
      intro u v hu hv
      exact ⟨hLn L₀ hL₀ u hu.1 v (hL₀K hv), hNmem u hu.2 v (hL₀K hv)⟩
    have hbot : L₀ ⊓ N = ⊥ := by
      have := hDn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L₀ ⊓ N).subgroupOf L₀) with h1 | h1
      · refine eq_bot_iff.mpr fun x hx => ?_
        have hx' : (⟨x, hx.1⟩ : L₀) ∈ (L₀ ⊓ N).subgroupOf L₀ := hx
        rw [h1, Subgroup.mem_bot] at hx'
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
      · exfalso
        refine hcase fun x hx => ?_
        have hx' : (⟨x, hx⟩ : L₀) ∈ (L₀ ⊓ N).subgroupOf L₀ := by rw [h1]; trivial
        exact (Subgroup.mem_inf.mp hx').2
    have hcomm₀ : ∀ l ∈ L₀, ∀ n ∈ N, n * l = l * n := by
      intro l hl n hn
      have h1 : l * n * l⁻¹ * n⁻¹ ∈ L₀ ⊓ N := by
        refine ⟨?_, ?_⟩
        · have := hLn L₀ hL₀ l⁻¹ (L₀.inv_mem hl) n (hNK hn)
          have h2 : l * (n * l⁻¹ * n⁻¹) ∈ L₀ := L₀.mul_mem hl (by simpa [mul_assoc] using this)
          simpa [mul_assoc] using h2
        · exact N.mul_mem (hNmem n hn l (hL₀K hl)) (N.inv_mem hn)
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    have hcomm : ∀ L ∈ lcal (θ f), ∀ l ∈ L, ∀ n ∈ N, n * l = l * n := by
      intro L hL l hl n hn
      obtain ⟨a, ha, rfl⟩ := d.exists_conj_A hL₀ hL
      obtain ⟨l₀, hl₀, rfl⟩ := hl
      have hmapN : N.map (MulAut.conj a⁻¹).toMonoidHom = N :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNA (A.inv_mem ha))
      have hn' : a⁻¹ * n * a ∈ N := by
        rw [← hmapN]
        exact ⟨n, hn, by simp⟩
      have := hcomm₀ l₀ hl₀ _ hn'
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
      calc n * (a * l₀ * a⁻¹) = a * ((a⁻¹ * n * a) * l₀) * a⁻¹ := by group
        _ = a * (l₀ * (a⁻¹ * n * a)) * a⁻¹ := by rw [this]
        _ = (a * l₀ * a⁻¹) * n := by group
    have hNc : N ≤ θ f ⊓ Subgroup.centralizer (kOf (θ f) : Set G) := by
      intro n hn
      refine ⟨kOf_le (θ f) (hNK hn), Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      rw [← hD.sSup_eq] at hk
      have hk' : k ∈ Subgroup.centralizer ({n} : Set G) := by
        refine (sSup_le (fun L hL l hl => ?_) : sSup (lcal (θ f)) ≤ _) hk
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm L hL l hl n hn).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp hk'
    rw [d.inf_centralizer_kOf_eq_bot, le_bot_iff] at hNc
    exact hN1 hNc

omit [Finite G] in
theorem eq_bot_of_isNilpotent_of_isSemisimple [Finite G] {Z : Subgroup G} (hss : IsSemisimple Z)
    (hn : Group.IsNilpotent ↥Z) : Z = ⊥ := by
  have hD := hss.isDirectProduct_lcal
  rw [← hD.sSup_eq, eq_bot_iff]
  refine sSup_le fun J hJ => ?_
  exfalso
  have hJZ : J ≤ Z := lcal_le hJ
  have : Group.IsNilpotent ↥J :=
    Thm210.isNilpotent_of_injective (Subgroup.inclusion hJZ) (Subgroup.inclusion_injective hJZ)
  exact not_isSolvable_of_mem_lcal hJ inferInstance

theorem Data.kOf_le_kOf
    (d : Data h E f) {X : Subgroup G} (hX : X ∈ assoc p A θ)
    (hKX : kOf (θ f) ≤ X) : kOf (θ f) ≤ kOf X := by
  have hθ := h.hyp.nearFunctor
  have hsol := d.sol_eq_bot_of_le hX hKX
  have hss : IsSemisimple (kOf X) := isSemisimple_kOf hsol
  have hAZ : Admits A (kOf X) := hX.1.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hNK : kOf (θ f) ⊓ kOf X ≤ kOf (θ f) := inf_le_left
  have hNn : ((kOf (θ f) ⊓ kOf X).subgroupOf (kOf (θ f))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNK]
    intro u v hu hv
    exact ⟨(kOf (θ f)).mul_mem ((kOf (θ f)).mul_mem hv hu.1) ((kOf (θ f)).inv_mem hv),
      (Subgroup.mem_normalizer_iff.mp (Thm41Aux.le_normalizer_kOf X (hKX hv)) u).mp hu.2⟩
  have hNA : Admits A (kOf (θ f) ⊓ kOf X) := Admits.inf d.admits_kOf hAZ
  rcases d.eq_bot_or_eq_kOf hNK hNn hNA with h0 | h1
  · exfalso
    have hfix : kOf X ⊓ Subgroup.centralizer {f} = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyZ, hyf⟩
      have hyX : y ∈ X := kOf_le X hyZ
      have hyθ : y ∈ θ f := hX.2.2.1 f d.mem d.ne_one ⟨hyX, hyf⟩
      have hyC : y ∈ X ⊓ Subgroup.centralizer (kOf (θ f) : Set G) := by
        refine ⟨hyX, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
        have h2 : k * y * k⁻¹ * y⁻¹ ∈ kOf (θ f) ⊓ kOf X := by
          refine ⟨?_, ?_⟩
          · have hy' := (Subgroup.mem_normalizer_iff.mp
              (Thm41Aux.le_normalizer_kOf (θ f) hyθ) k⁻¹).mp ((kOf (θ f)).inv_mem hk)
            have := (kOf (θ f)).mul_mem hk hy'
            simpa [mul_assoc] using this
          · have h3 := (Subgroup.mem_normalizer_iff.mp
              (Thm41Aux.le_normalizer_kOf X (hKX hk)) y).mp hyZ
            exact (kOf X).mul_mem h3 ((kOf X).inv_mem hyZ)
        rw [h0, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
        exact h2
      rw [d.cenIn_eq_bot hX] at hyC
      exact hyC
    have := Fact.mk hθ.prime
    have hord : orderOf f = p := orderOf_eq_prime (hθ.elemAbelian.2 f d.mem) d.ne_one
    have hnil := Thompson.fpf_nilpotent hθ.prime hord (hAZ d.mem) hfix
    have hZ0 : kOf X = ⊥ := eq_bot_of_isNilpotent_of_isSemisimple hss hnil
    have hX0 : X = ⊥ := by
      have := centralizer_kOf_eq_bot hsol
      rwa [hZ0, Thm211.centralizer_bot, inf_top_eq] at this
    obtain ⟨L₀, hL₀⟩ := d.lcal_nonempty
    have hL₀K : L₀ ≤ ⊥ := by
      rw [← hX0]
      exact (lcal_le (d.lcal_kOf ▸ hL₀ : L₀ ∈ lcal (kOf (θ f)))).trans hKX
    rw [le_bot_iff] at hL₀K
    subst hL₀K
    exact not_isSolvable_of_mem_lcal hL₀ inferInstance
  · exact h1 ▸ inf_le_right

theorem Data.le_apply_of_kOf_eq
    (d : Data h E f) {X : Subgroup G} (hX : X ∈ assoc p A θ)
    (hKX : kOf (θ f) ≤ X) (heq : kOf X = kOf (θ f)) : X ≤ θ f := by
  have hθ := h.hyp.nearFunctor
  have hsol := d.sol_eq_bot_of_le hX hKX
  have hC : X ⊓ Subgroup.centralizer (kOf (θ f) : Set G) = ⊥ := by
    have := centralizer_kOf_eq_bot hsol
    rwa [heq] at this
  have hfK : ∀ k ∈ kOf (θ f), f * k * f⁻¹ = k := fun k hk => by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp
      (hθ.isFunctor.le_centralizer f d.mem d.ne_one (kOf_le _ hk))
    rw [← h1]
    group
  intro x hx
  have hfx : f * x * f⁻¹ ∈ X := hX.1 d.mem |> fun hf => (Subgroup.mem_normalizer_iff.mp hf x).mp hx
  have hy : (f * x * f⁻¹)⁻¹ * x ∈ X ⊓ Subgroup.centralizer (kOf (θ f) : Set G) := by
    refine ⟨X.mul_mem (X.inv_mem hfx) hx, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    have hxn : x * k * x⁻¹ ∈ kOf (θ f) := by
      have := (Subgroup.mem_normalizer_iff.mp (Thm41Aux.le_normalizer_kOf X hx) k).mp
        (heq ▸ hk)
      rwa [heq] at this
    have h2 := hfK _ hxn
    have h3 := hfK _ hk
    have h2' : (x * k * x⁻¹) * f⁻¹ = f⁻¹ * (x * k * x⁻¹) := by
      calc (x * k * x⁻¹) * f⁻¹ = f⁻¹ * (f * (x * k * x⁻¹) * f⁻¹) := by group
        _ = f⁻¹ * (x * k * x⁻¹) := by rw [h2]
    symm
    calc ((f * x * f⁻¹)⁻¹ * x) * k = f * x⁻¹ * (f⁻¹ * (x * k * x⁻¹)) * x := by group
      _ = f * x⁻¹ * ((x * k * x⁻¹) * f⁻¹) * x := by rw [h2']
      _ = (f * k * f⁻¹) * (f * x⁻¹ * f⁻¹ * x) := by group
      _ = k * ((f * x * f⁻¹)⁻¹ * x) := by rw [h3]; group
  rw [hC, Subgroup.mem_bot] at hy
  have hfx' : f * x * f⁻¹ = x := by
    have := inv_mul_eq_one.mp hy
    exact this
  exact hX.2.2.1 f d.mem d.ne_one ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr
    (by rw [mul_inv_eq_iff_eq_mul] at hfx'; exact hfx'.symm)⟩

theorem Data.kOf_ne_bot
    (d : Data h E f) : kOf (θ f) ≠ ⊥ := by
  obtain ⟨L, hL⟩ := d.lcal_nonempty
  intro h0
  have hL0 : L ≤ ⊥ := h0 ▸ lcal_le (d.lcal_kOf ▸ hL : L ∈ lcal (kOf (θ f)))
  rw [le_bot_iff] at hL0
  subst hL0
  exact not_isSolvable_of_mem_lcal hL inferInstance

theorem Data.not_mem_sup_symm (d : Data h E f) {c : G} (dc : Data h E c)
    (hcn : c ∉ E ⊔ Subgroup.zpowers f) : f ∉ E ⊔ Subgroup.zpowers c := by
  intro hf
  have hle : E ⊔ Subgroup.zpowers f ≤ E ⊔ Subgroup.zpowers c :=
    _root_.sup_le le_sup_left (Subgroup.zpowers_le.mpr hf)
  have heq : E ⊔ Subgroup.zpowers f = E ⊔ Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [d.card_sup, dc.card_sup])
  exact hcn (by rw [heq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c))

theorem Data.kOf_inf_centralizer_comm
    (d : Data h E f) {c : G} (dc : Data h E c)
    (hcn : c ∉ E ⊔ Subgroup.zpowers f) :
    kOf (θ c) ⊓ Subgroup.centralizer ({f} : Set G) =
      kOf (θ f) ⊓ Subgroup.centralizer ({c} : Set G) := by
  have hfn := d.not_mem_sup_symm dc hcn
  rw [← dc.kOf_plane d.mem hfn, sup_comm, d.kOf_plane dc.mem hcn]

theorem exists_component_normalizer {Z K : Subgroup G} (hZ : IsSemisimple Z)
    (hK : IsSemisimple K) (hKZ : K ≤ Z) (hproj : ∀ J ∈ lcal Z, projIn (lcal Z) J K = J)
    {J : Subgroup G} (hJ : J ∈ lcal Z) :
    ∃ R ∈ lcal K, ∀ g : G, g ∈ Subgroup.normalizer (Z : Set G) →
      g ∈ Subgroup.normalizer (K : Set G) → g ∈ Subgroup.normalizer (J : Set G) →
      g ∈ Subgroup.normalizer (R : Set G) := by
  have hZd := hZ.isDirectProduct_lcal
  obtain ⟨-, -, hJs, hJnc⟩ := mem_lcal_iff.mp hJ
  let φ : ↥K →* ↥J := (hZd.coord hJ).comp (Subgroup.inclusion hKZ)
  set κ : Subgroup G := K ⊓ sSup (lcal Z \ {J}) with hκ
  have hker : κ.subgroupOf K = φ.ker := by
    ext k
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hκ]
    constructor
    · rintro ⟨-, hk⟩
      exact (hZd.coord_eq_one_iff hJ _).mpr hk
    · intro hk
      exact ⟨k.2, (hZd.coord_eq_one_iff hJ _).mp hk⟩
  have hκn : (κ.subgroupOf K).Normal := by
    rw [hker]
    exact MonoidHom.normal_ker φ
  set R : Subgroup G := K ⊓ Subgroup.centralizer (κ : Set G) with hR
  have hdp : IsDirectPair κ R K := hK.isDirectPair_of_normal inf_le_left hκn
  let ψ : ↥R →* ↥J := φ.comp (Subgroup.inclusion (inf_le_left : R ≤ K))
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : G) ∈ κ := by
      have : (Subgroup.inclusion (inf_le_left : R ≤ K) x) ∈ φ.ker := hx
      rw [← hker] at this
      exact this
    have h2 : (x : G) ∈ κ ⊓ R := ⟨h1, x.2⟩
    rw [hdp.inf_eq_bot, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective ψ := by
    intro y
    have hy : (y : G) ∈ projIn (lcal Z) J K := by
      rw [hproj J hJ]
      exact y.2
    obtain ⟨k, hkK, hky⟩ := (hZd.mem_projIn_iff hJ).mp hy
    have hk' : (k : G) ∈ κ ⊔ R := hdp.sup_eq ▸ hkK
    obtain ⟨m, hm, r, hr, hmr⟩ := (mem_sup_iff_of_commute hdp.commute).mp hk'
    have hmZ : m ∈ Z := hKZ hm.1
    have hrZ : r ∈ Z := hKZ hr.1
    have hkeq : k = ⟨m, hmZ⟩ * ⟨r, hrZ⟩ := Subtype.ext hmr.symm
    have hcm : hZd.coord hJ ⟨m, hmZ⟩ = 1 := (hZd.coord_eq_one_iff hJ _).mpr hm.2
    refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
    rw [← hky, hkeq, map_mul, hcm, one_mul]
    rfl
  let e : ↥R ≃* ↥J := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have : IsSimpleGroup ↥J := hJs
  have hRs : IsSimpleGroup ↥R := e.isSimpleGroup
  have hRnc : ¬ IsMulCommutative ↥R := fun h' => hJnc ((isMulCommutative_congr e).mp h')
  have hκmem : ∀ x ∈ κ, ∀ v ∈ K, v * x * v⁻¹ ∈ κ := fun x hx v hv =>
    (Subgroup.normal_subgroupOf_iff inf_le_left).mp hκn x v hx hv
  have hconj : ∀ u ∈ R, ∀ v ∈ K, v * u * v⁻¹ ∈ R := by
    intro u hu v hv
    refine ⟨K.mul_mem (K.mul_mem hv hu.1) (K.inv_mem hv),
      Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx' : v⁻¹ * x * v⁻¹⁻¹ ∈ κ := hκmem x hx v⁻¹ (K.inv_mem hv)
    have h1 := Subgroup.mem_centralizer_iff.mp hu.2 _ hx'
    simp only [inv_inv] at h1
    calc x * (v * u * v⁻¹) = v * ((v⁻¹ * x * v) * u) * v⁻¹ := by group
      _ = v * (u * (v⁻¹ * x * v)) * v⁻¹ := by rw [h1]
      _ = (v * u * v⁻¹) * x := by group
  have hRn : (R.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    exact fun u v hu hv => hconj u hu v hv
  have hRmem : R ∈ lcal K := mem_lcal_iff.mpr ⟨inf_le_left, hRn.isSubnormal, hRs, hRnc⟩
  refine ⟨R, hRmem, fun g hgZ hgK hgJ => ?_⟩
  have hperm : ∀ J' ∈ lcal Z, J'.map (MulAut.conj g).toMonoidHom ∈ lcal Z :=
    fun J' hJ' => map_conj_mem_lcal hJ' hgZ
  have hperm' : ∀ J' ∈ lcal Z, J'.map (MulAut.conj g⁻¹).toMonoidHom ∈ lcal Z :=
    fun J' hJ' => map_conj_mem_lcal hJ' ((Subgroup.normalizer (Z : Set G)).inv_mem hgZ)
  have hJg : J.map (MulAut.conj g).toMonoidHom = J :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgJ
  have hgκ : g ∈ Subgroup.normalizer (κ : Set G) := by
    refine mem_normalizer_of_conj_mem fun y hy =>
      ⟨(Subgroup.mem_normalizer_iff.mp hgK y).mp hy.1, ?_⟩
    have := (Nonsolv.Diag.conj_mem_sSup_diff_map_iff hperm hperm').mpr hy.2
    rwa [hJg] at this
  refine mem_normalizer_of_conj_mem fun y hy => ⟨(Subgroup.mem_normalizer_iff.mp hgK y).mp hy.1,
    Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ κ :=
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (κ : Set G)).inv_mem hgκ) x).mp hx
  have h1 := Subgroup.mem_centralizer_iff.mp hy.2 _ hx'
  simp only [inv_inv] at h1
  calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = (g * y * g⁻¹) * x := by group


theorem Data.eq_or_eq_of_plane
    {c : G} (dc : Data h E c) {f : G} (hf : f ∈ A)
    (hfn : f ∉ E ⊔ Subgroup.zpowers c) {U : Subgroup G} (hUK : U ≤ kOf (θ c))
    (hUA : Admits A U) (hU : kOf (θ c) ⊓ Subgroup.centralizer ({f} : Set G) ≤ U) :
    U = kOf (θ c) ⊓ Subgroup.centralizer ({f} : Set G) ∨ U = kOf (θ c) := by
  have hθ := h.hyp.nearFunctor
  refine eq_or_eq_of_singleOrbit hθ.prime (isSemisimple_kOf dc.sol_eq_bot) (dc.admits_kOf hf)
    (hθ.elemAbelian.2 f hf) ?_ ?_ hUK (hUA hf) hU
  · intro J hJ hfJ
    have hJ' : J ∈ lcal (θ c) := dc.lcal_kOf ▸ hJ
    have hmem : f ∈ A ⊓ Subgroup.normalizer (J : Set G) := ⟨hf, hfJ⟩
    exact hfn (dc.inf_normalizer_eq hJ' ▸ hmem)
  · intro J hJ J' hJ'
    obtain ⟨k, hk⟩ := dc.exists_zpow_conj hf hfn (dc.lcal_kOf ▸ hJ) (dc.lcal_kOf ▸ hJ')
    exact ⟨f ^ k, Subgroup.zpow_mem_zpowers f k, hk⟩

omit [Finite G] in
theorem isPerfect_of_simple {J : Subgroup G} (hs : IsSimpleGroup ↥J) (hnc : ¬ IsMulCommutative ↥J) :
    Group.IsPerfect ↥J := by
  have hnc' : ∃ a b : ↥J, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hnc (isMulCommutative_iff.mpr hcon)
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc').1.1

theorem Data.card_sup_zpowers (d : Data h E f) {b : G} (hb : b ∈ A)
    (hbf : b ∉ Subgroup.zpowers f) :
    Nat.card (Subgroup.zpowers f ⊔ Subgroup.zpowers b : Subgroup G) = p ^ 2 := by
  have hθ := h.hyp.nearFunctor
  have hb1 : b ≠ 1 := fun h1 => hbf (h1 ▸ one_mem _)
  have hcb : Nat.card (Subgroup.zpowers b) = p :=
    Sec6Gen.card_zpowers_of_pow_eq_one hθ.prime (hθ.elemAbelian.2 b hb) hb1
  have hnle : ¬ Subgroup.zpowers b ≤ Subgroup.zpowers f := fun hle =>
    hbf (hle (Subgroup.mem_zpowers b))
  have hd := inf_eq_bot_of_not_le hθ.prime hcb hnle
  rw [card_sup_of_commute (fun x hx y hy => comm_of_mem_of_isMulCommutative hθ.elemAbelian.1
    (Subgroup.zpowers_le.mpr d.mem hx) (Subgroup.zpowers_le.mpr hb hy)) hd, d.card_zpowers, hcb,
    sq]

theorem Data.exists_good_line
    (d : Data h E f) {Z : Subgroup G} (hZ : Z ∈ assoc p A θ)
    (hKZ : kOf (θ f) ≤ Z) :
    ∃ c ∈ A, c ∉ E ⊔ Subgroup.zpowers f ∧
      perfRes (Z ⊓ Subgroup.centralizer ({c} : Set G)) =
        kOf (θ f) ⊓ Subgroup.centralizer ({c} : Set G) := by
  have hθ := h.hyp.nearFunctor
  by_contra hcon
  push Not at hcon
  have key : ∀ c ∈ A, c ∉ E ⊔ Subgroup.zpowers f → kOf (θ c) ≤ Z := by
    intro c hc hcn
    have dc : Data h E c := ⟨d.distE, hc, fun hcE => hcn (Subgroup.mem_sup_left hcE)⟩
    have hfn := d.not_mem_sup_symm dc hcn
    have hcomm := d.kOf_inf_centralizer_comm dc hcn
    have hPle : perfRes (Z ⊓ Subgroup.centralizer ({c} : Set G)) ≤ kOf (θ c) := by
      rw [← dc.perfRes_eq]
      exact Sec6S33.perfRes_mono (le_trans (inf_le_inf_right _ le_rfl) (hZ.2.2.1 c hc dc.ne_one))
    have hKB : kOf (θ c) ⊓ Subgroup.centralizer ({f} : Set G) ≤
        perfRes (Z ⊓ Subgroup.centralizer ({c} : Set G)) := by
      rw [hcomm]
      have hperf : Group.IsPerfect ↥(kOf (θ f) ⊓ Subgroup.centralizer ({c} : Set G)) := by
        rw [← d.kOf_plane dc.mem hcn]
        obtain ⟨-, -, hsimple, hnc⟩ := mem_lcal_iff.mp (d.kOf_plane_mem_lcal dc.mem hcn)
        exact isPerfect_of_simple hsimple hnc
      exact Sec6S33.le_perfRes_of_isPerfect hperf (inf_le_inf_right _ hKZ)
    have hA : Admits A (perfRes (Z ⊓ Subgroup.centralizer ({c} : Set G))) :=
      Sec6S33.admits_perfRes (Admits.inf hZ.1 (admits_centralizer_singleton
        (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
          (comm_of_mem_of_isMulCommutative hθ.elemAbelian.1 hc ha).symm)))
    rcases dc.eq_or_eq_of_plane d.mem hfn hPle hA hKB with h1 | h1
    · exact absurd (h1.trans hcomm) (hcon c hc hcn)
    · exact h1 ▸ (Sec6S33.perfRes_le _).trans inf_le_left
  obtain ⟨e₀, he₀, hen₀⟩ := d.exists_mem_sdiff
  have hB : Subgroup.zpowers f ⊔ Subgroup.zpowers e₀ ∈ rSetN p A θ 2 :=
    d.plane_mem_rSetN_two he₀ hen₀
  have h64 := h.lemma64 hB
  have hW : wsub p A θ ≤ Z := by
    rw [← h64]
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    have hbA : b ∈ A := d.plane_le he₀ hb
    by_cases hbf : b ∈ Subgroup.zpowers f
    · have hcb : Nat.card (Subgroup.zpowers b) = p :=
        Sec6Gen.card_zpowers_of_pow_eq_one hθ.prime (hθ.elemAbelian.2 b hbA) hb1
      have hzb : Subgroup.zpowers b = Subgroup.zpowers f :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbf) (by rw [d.card_zpowers, hcb])
      have hθb : θ b = θ f := by
        rw [← hθ.isFunctor.thetaOf_zpowers hbA hb1, hzb,
          hθ.isFunctor.thetaOf_zpowers d.mem d.ne_one]
      rw [hθb]
      exact hKZ
    · have hbn : b ∉ E ⊔ Subgroup.zpowers f := by
        intro hbE
        have hcard := d.card_sup_zpowers hbA hbf
        have hS1 : Subgroup.zpowers f ⊔ Subgroup.zpowers b ≤
            Subgroup.zpowers f ⊔ Subgroup.zpowers e₀ :=
          _root_.sup_le le_sup_left (Subgroup.zpowers_le.mpr hb)
        have hS2 : Subgroup.zpowers f ⊔ Subgroup.zpowers b ≤ E ⊔ Subgroup.zpowers f :=
          _root_.sup_le le_sup_right (Subgroup.zpowers_le.mpr hbE)
        have e1 : Subgroup.zpowers f ⊔ Subgroup.zpowers b =
            Subgroup.zpowers f ⊔ Subgroup.zpowers e₀ :=
          Subgroup.eq_of_le_of_card_ge hS1 (by rw [hcard, d.card_plane he₀ hen₀])
        have e2 : Subgroup.zpowers f ⊔ Subgroup.zpowers b = E ⊔ Subgroup.zpowers f :=
          Subgroup.eq_of_le_of_card_ge hS2 (by rw [hcard, d.card_sup])
        exact hen₀ (e2 ▸ e1 ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers e₀))
      exact key b hbA hbn
  exact h.notComplete ⟨Z, hZ, fun Y hY => le_trans (le_sSup hY) hW⟩

theorem Data.projIn_eq_of_le
    (d : Data h E f) {X : Subgroup G} (hX : X ∈ assoc p A θ)
    (hKX : kOf (θ f) ≤ X) :
    ∀ J ∈ lcal (kOf X), projIn (lcal (kOf X)) J (kOf (θ f)) = J := by
  have hθ := h.hyp.nearFunctor
  have hsol := d.sol_eq_bot_of_le hX hKX
  have hX1 : X ≠ ⊥ := fun h0 => d.kOf_ne_bot (le_bot_iff.mp (h0 ▸ hKX))
  have hnear : NearAsolvAction p A X :=
    { prime := hθ.prime
      odd := hθ.odd
      elemAbelian := hθ.elemAbelian
      admits := hX.1
      nearPSolvable := hX.2.2.2.1
      solvable_cen := hX.2.2.2.2 }
  have hss : SemisimpleAction p A (kOf X) := Thm34.semisimpleAction_kOf hnear hsol hX1
  have hZK : kOf (θ f) ≤ kOf X := d.kOf_le_kOf hX hKX
  have hAZ : Admits A (kOf X) := hX.1.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hZ : kOf X ∈ assoc p A θ := mem_assoc_of_le hθ.prime hX (kOf_le X) hAZ
  have hDA : Admits (cenIn (kOf X) (A : Set G) ⊔ A) (kOf (θ f)) :=
    _root_.sup_le (((cenIn_le_dsub hZ).trans (dsub_le_apply d.mem d.ne_one)).trans
      (Thm41Aux.le_normalizer_kOf (θ f))) d.admits_kOf
  have hperf : Group.IsPerfect ↥(kOf (θ f)) := d.perfRes_eq ▸ Sec6S33.isPerfect_perfRes (θ f)
  intro J hJ
  have hG := hss.isDirectProduct_lcal
  have hns : ¬ Group.IsSolvable ↥(projIn (lcal (kOf X)) J (kOf (θ f))) := by
    intro hsolv
    have hperfQ := Thm33b.isPerfect_projIn hG hJ hZK hperf
    have hQbot : projIn (lcal (kOf X)) J (kOf (θ f)) = ⊥ := by
      by_contra hne
      have : Nontrivial ↥(projIn (lcal (kOf X)) J (kOf (θ f))) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      exact Group.IsPerfect.not_isSolvable _ hsolv
    have hJC : J ≤ X ⊓ Subgroup.centralizer (kOf (θ f) : Set G) := by
      intro j hj
      refine ⟨kOf_le X (lcal_le hJ hj), Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have hxK : x ∈ kOf X := hZK hx
      have hmem : ((hG.coord hJ ⟨x, hxK⟩ : J) : G) ∈ projIn (lcal (kOf X)) J (kOf (θ f)) :=
        (IsDirectProduct.mem_projIn_iff hG hJ).mpr ⟨⟨x, hxK⟩, hx, rfl⟩
      rw [hQbot, Subgroup.mem_bot] at hmem
      have h2 : x ∈ sSup (lcal (kOf X) \ {J}) :=
        (hG.coord_eq_one_iff hJ ⟨x, hxK⟩).mp (Subtype.ext hmem)
      exact (hG.commute_sSup_diff hJ j hj x h2).eq.symm
    rw [d.cenIn_eq_bot hX, le_bot_iff] at hJC
    obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hJ
    rw [hJC] at hnc
    exact hnc inferInstance
  exact (thm210g hss hZK hDA hJ hns).1

theorem Data.kOf_eq_of_le
    (d : Data h E f) {X : Subgroup G} (hX : X ∈ assoc p A θ)
    (hKX : kOf (θ f) ≤ X) : kOf X = kOf (θ f) := by
  have hθ := h.hyp.nearFunctor
  have hsol := d.sol_eq_bot_of_le hX hKX
  have hss : IsSemisimple (kOf X) := isSemisimple_kOf hsol
  have hZK : kOf (θ f) ≤ kOf X := d.kOf_le_kOf hX hKX
  have hAZ : Admits A (kOf X) := hX.1.trans (Thm211.normalizer_le_normalizer_kOf X)
  have hZ : kOf X ∈ assoc p A θ := mem_assoc_of_le hθ.prime hX (kOf_le X) hAZ
  have hproj := d.projIn_eq_of_le hX hKX
  obtain ⟨c, hc, hcn, hgood⟩ := d.exists_good_line hZ hZK
  have dc : Data h E c := ⟨d.distE, hc, fun hcE => hcn (Subgroup.mem_sup_left hcE)⟩
  have hKss : IsSemisimple (kOf (θ f)) := isSemisimple_kOf d.sol_eq_bot
  have hmove : ∀ J ∈ lcal (kOf X), c ∉ Subgroup.normalizer (J : Set G) := by
    intro J hJ hcJ
    obtain ⟨R, hR, hRn⟩ := exists_component_normalizer hss hKss hZK hproj hJ
    have hcR := hRn c (hAZ hc) (d.admits_kOf hc) hcJ
    have hR' : R ∈ lcal (θ f) := d.lcal_kOf ▸ hR
    have hmem : c ∈ A ⊓ Subgroup.normalizer (R : Set G) := ⟨hc, hcR⟩
    exact hcn (d.inf_normalizer_eq hR' ▸ hmem)
  have hsimple : IsSimpleGroup ↥(perfRes (kOf X ⊓ Subgroup.centralizer ({c} : Set G))) := by
    rw [hgood, ← d.kOf_plane dc.mem hcn]
    exact (mem_lcal_iff.mp (d.kOf_plane_mem_lcal dc.mem hcn)).2.2.1
  obtain ⟨horb, hperf⟩ := singleOrbit_of_isSimple_perfRes hθ.prime hss (hAZ hc)
    (hθ.elemAbelian.2 c hc) hmove hsimple
  have hCle : kOf X ⊓ Subgroup.centralizer ({c} : Set G) ≤ kOf (θ f) := by
    refine hperf.trans ?_
    rw [hgood]
    exact inf_le_left
  rcases eq_or_eq_of_singleOrbit hθ.prime hss (hAZ hc) (hθ.elemAbelian.2 c hc) hmove horb hZK
    (d.admits_kOf hc) hCle with h1 | h1
  · exfalso
    obtain ⟨L, hL⟩ := d.lcal_nonempty
    have hLK : L ≤ kOf (θ f) := lcal_le (d.lcal_kOf ▸ hL : L ∈ lcal (kOf (θ f)))
    have hLc : c ∈ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have : y ∈ kOf X ⊓ Subgroup.centralizer ({c} : Set G) := h1 ▸ hLK hy
      exact Subgroup.mem_centralizer_singleton_iff.mp this.2
    have hmem : c ∈ A ⊓ Subgroup.normalizer (L : Set G) :=
      ⟨hc, Subgroup.centralizer_le_normalizer _ hLc⟩
    exact hcn (d.inf_normalizer_eq hL ▸ hmem)
  · exact h1.symm

theorem DistE.maximal
    (h : Counterexample p A θ) {E : Subgroup G} (hE : DistE p A θ E) :
    ∀ f ∈ A, f ∉ E → ∀ X ∈ assoc p A θ, kOf (θ f) ≤ X → X ≤ θ f := by
  intro f hf hfE X hX hKX
  have d : Data h E f := ⟨hE, hf, hfE⟩
  exact d.le_apply_of_kOf_eq hX hKX (d.kOf_eq_of_le hX hKX)

end Sec6S34

end CFSG.SignalizerFunctorTheorem.McBride.Near
