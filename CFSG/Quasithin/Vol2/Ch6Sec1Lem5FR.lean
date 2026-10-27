module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FQ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

section Inner

variable {Γ : Type*} [Group Γ]

theorem exists_inner_of_odd_ch615 [Finite Γ] {F Y S : Subgroup Γ}
    (hout : ∀ α : MulAut ↥F, Odd (orderOf α) → ∃ g : ↥F, α = MulAut.conj g)
    (hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1)
    (hS2 : IsPGroup 2 S) (hSF : S ≤ F) (hNS : ∀ g ∈ F, (∀ s ∈ S, g * s * g⁻¹ ∈ S) → g ∈ S)
    (hself : ∀ R : Subgroup Γ, S ≤ R → R ≤ F → R ≠ S → Group.IsSolvable ↥R →
      ∀ g ∈ F, (∀ r ∈ R, g * r * g⁻¹ ∈ R) → g ∈ R)
    (hSY : S ≤ Y) (hY : Group.IsSolvable ↥Y) {δ : Γ} (hδY : δ ∈ Y)
    (hδN : δ ∈ Subgroup.normalizer (F : Set Γ)) (hδodd : Odd (orderOf δ)) :
    ∃ g ∈ F, (∀ x ∈ F, δ * x * δ⁻¹ = g * x * g⁻¹) ∧ (g = 1 ∨ g ∈ Y) := by
  classical
  set φ := F.normalizerMonoidHom with hφ
  set α := φ ⟨δ, hδN⟩ with hα
  have hαo : orderOf α ∣ orderOf δ := by
    have := orderOf_map_dvd φ ⟨δ, hδN⟩
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨g, hg⟩ := hout α (Odd.of_dvd_nat hδodd hαo)
  have hδg : ∀ x ∈ F, δ * x * δ⁻¹ = (g : Γ) * x * (g : Γ)⁻¹ := fun x hx => by
    have := congrArg (fun β : MulAut ↥F => ((β ⟨x, hx⟩ : ↥F) : Γ)) hg
    simpa [hα, hφ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using this
  have hinj : Function.Injective (MulAut.conj : ↥F →* MulAut ↥F) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    apply Subtype.ext
    refine hZ y y.2 fun x hx => ?_
    have := congrArg (fun β : MulAut ↥F => ((β ⟨x, hx⟩ : ↥F) : Γ)) hy
    simp only [MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
    calc (y : Γ) * x = (y : Γ) * x * (y : Γ)⁻¹ * (y : Γ) := by group
      _ = x * y := by rw [this]
  have hgo : orderOf (g : Γ) ∣ orderOf δ := by
    have : orderOf (g : Γ) = orderOf α := by
      rw [hg, orderOf_injective _ hinj, Subgroup.orderOf_coe]
    rw [this]
    exact hαo
  have hgodd : Odd (orderOf (g : Γ)) := Odd.of_dvd_nat hδodd hgo
  refine ⟨g, g.2, hδg, ?_⟩
  by_cases hg1 : (g : Γ) = 1
  · exact Or.inl hg1
  right
  have hgS : (g : Γ) ∉ S := fun hgS => hg1 (eq_one_of_odd_of_mem_l32_ch615 hS2 hgS hgodd)
  have hex : ∃ s ∈ S, (g : Γ) * s * (g : Γ)⁻¹ ∉ S := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    exact hgS (hNS g g.2 hall)
  obtain ⟨s, hs, hgs⟩ := hex
  have hsG : s ∈ F := hSF hs
  have hxe : δ * s * δ⁻¹ = (g : Γ) * s * (g : Γ)⁻¹ := hδg s hsG
  have hxY : δ * s * δ⁻¹ * s⁻¹ ∈ Y :=
    Y.mul_mem (Y.mul_mem (Y.mul_mem hδY (hSY hs)) (Y.inv_mem hδY)) (Y.inv_mem (hSY hs))
  have hxG : δ * s * δ⁻¹ * s⁻¹ ∈ F := by
    rw [hxe]
    exact F.mul_mem (F.mul_mem (F.mul_mem g.2 hsG) (F.inv_mem g.2)) (F.inv_mem hsG)
  have hxS : δ * s * δ⁻¹ * s⁻¹ ∉ S := fun hx => hgs (by
    have := S.mul_mem hx hs
    rwa [hxe, inv_mul_cancel_right] at this)
  have hRS : Y ⊓ F ≠ S := fun h => hxS (h ▸ ⟨hxY, hxG⟩)
  have hRs : Group.IsSolvable ↥(Y ⊓ F) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (inf_le_left : Y ⊓ F ≤ Y))
  have hgR : ∀ r ∈ Y ⊓ F, (g : Γ) * r * (g : Γ)⁻¹ ∈ Y ⊓ F := by
    intro r hr
    have hrG : r ∈ F := hr.2
    rw [← hδg r hrG]
    refine ⟨Y.mul_mem (Y.mul_mem hδY hr.1) (Y.inv_mem hδY), ?_⟩
    rw [hδg r hrG]
    exact F.mul_mem (F.mul_mem g.2 hrG) (F.inv_mem g.2)
  exact (hself (Y ⊓ F) (le_inf hSY hSF) inf_le_right hRS hRs g g.2 hgR).1

theorem isPGroup_inf_sup_ch615 {X F T₀ : Subgroup Γ}
    (hXF : X ≤ Subgroup.normalizer (F : Set Γ)) (hT₀X : T₀ ≤ X) (hT₀ : IsPGroup 2 ↥T₀)
    (hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1) :
    IsPGroup 2 ↥(F ⊓ ((X ⊓ Subgroup.centralizer (F : Set Γ)) ⊔ T₀)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := X ⊓ Subgroup.centralizer (F : Set Γ) with hC
  have hT₀C : T₀ ≤ Subgroup.normalizer (C : Set Γ) := by
    intro t ht
    refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨fun hc => ?_, fun hc => ?_⟩
    · refine ⟨X.mul_mem (X.mul_mem (hT₀X ht) hc.1) (X.inv_mem (hT₀X ht)),
        Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have hx' : t⁻¹ * x * t ∈ F := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXF (hT₀X ht))) x).mp hx
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hx'
      calc x * (t * c * t⁻¹) = t * ((t⁻¹ * x * t) * c) * t⁻¹ := by group
        _ = t * (c * (t⁻¹ * x * t)) * t⁻¹ := by rw [h1]
        _ = t * c * t⁻¹ * x := by group
    · have ht' : t⁻¹ ∈ T₀ := T₀.inv_mem ht
      have hc' : t⁻¹ * (t * c * t⁻¹) * t⁻¹⁻¹ ∈ C := by
        refine ⟨X.mul_mem (X.mul_mem (hT₀X ht') hc.1) (X.inv_mem (hT₀X ht')),
          Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        have hx' : t * x * t⁻¹ ∈ F :=
          (Subgroup.mem_normalizer_iff.mp (hXF (hT₀X ht)) x).mp hx
        have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hx'
        calc x * (t⁻¹ * (t * c * t⁻¹) * t⁻¹⁻¹) = t⁻¹ * ((t * x * t⁻¹) * (t * c * t⁻¹)) * t := by
              group
          _ = t⁻¹ * ((t * c * t⁻¹) * (t * x * t⁻¹)) * t := by rw [h1]
          _ = t⁻¹ * (t * c * t⁻¹) * t⁻¹⁻¹ * x := by group
      simpa [mul_assoc] using hc'
  intro w
  have hw : (w : Γ) ∈ ((C ⊔ T₀ : Subgroup Γ) : Set Γ) := w.2.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left C T₀ hT₀C] at hw
  obtain ⟨c, hc, t, ht, hct⟩ := Set.mem_mul.mp hw
  obtain ⟨e, he⟩ := hT₀ ⟨t, ht⟩
  have ht2 : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  refine ⟨e, Subtype.ext ?_⟩
  have hact : ∀ m : ℕ, ∀ x ∈ F, (w : Γ) ^ m * x * ((w : Γ) ^ m)⁻¹ = t ^ m * x * (t ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro x _; simp
    | succ m ih =>
      intro x hx
      have htm : t ^ m * x * (t ^ m)⁻¹ ∈ F := by
        have : t ^ m ∈ T₀ := T₀.pow_mem ht m
        exact (Subgroup.mem_normalizer_iff.mp (hXF (hT₀X this)) x).mp hx
      have hcx := Subgroup.mem_centralizer_iff.mp hc.2 _ htm
      calc (w : Γ) ^ (m + 1) * x * ((w : Γ) ^ (m + 1))⁻¹
          = (w : Γ) * ((w : Γ) ^ m * x * ((w : Γ) ^ m)⁻¹) * (w : Γ)⁻¹ := by group
        _ = c * t * (t ^ m * x * (t ^ m)⁻¹) * (c * t)⁻¹ := by rw [ih x hx, hct]
        _ = c * (t * (t ^ m * x * (t ^ m)⁻¹) * t⁻¹) * c⁻¹ := by group
        _ = t * (t ^ m * x * (t ^ m)⁻¹) * t⁻¹ := by
          have htx : t * (t ^ m * x * (t ^ m)⁻¹) * t⁻¹ ∈ F := by
            exact (Subgroup.mem_normalizer_iff.mp (hXF (hT₀X ht)) _).mp htm
          have h2 := Subgroup.mem_centralizer_iff.mp hc.2 _ htx
          calc c * (t * (t ^ m * x * (t ^ m)⁻¹) * t⁻¹) * c⁻¹
              = (t * (t ^ m * x * (t ^ m)⁻¹) * t⁻¹) * c * c⁻¹ := by rw [h2]
            _ = t * (t ^ m * x * (t ^ m)⁻¹) * t⁻¹ := by group
        _ = t ^ (m + 1) * x * (t ^ (m + 1))⁻¹ := by group
  have hwF : (w : Γ) ^ 2 ^ e ∈ F := F.pow_mem w.2.1 _
  have h1 := hZ _ hwF fun x hx => by
    have := hact (2 ^ e) x hx
    rw [ht2, one_mul, inv_one, mul_one] at this
    calc (w : Γ) ^ 2 ^ e * x = (w : Γ) ^ 2 ^ e * x * ((w : Γ) ^ 2 ^ e)⁻¹ * (w : Γ) ^ 2 ^ e := by
          group
      _ = x * (w : Γ) ^ 2 ^ e := by rw [this]
  simpa using h1

end Inner

section Transfer

variable {W : Type*} [CommGroup W] [Finite W]

theorem mem_commV_sup_fixV_ch615 (hW : ∀ w : W, w ^ 2 = 1) {F S : Subgroup (MulAut W)}
    (hodd : ¬ 2 ∣ S.relIndex F) {w : W} (hw : ∀ s ∈ S, s w = w) :
    w ∈ commV F ⊔ fixV F := by
  classical
  have : Finite (MulAut W) := inferInstance
  have : Fintype (↥F ⧸ S.subgroupOf F) := Fintype.ofFinite _
  set φ : ↥F ⧸ S.subgroupOf F → W := fun q => ((q.out : ↥F) : MulAut W) w with hφdef
  have hφ : ∀ g : ↥F, φ (QuotientGroup.mk g) = (g : MulAut W) w := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (S.subgroupOf F) g
    simp only [hφdef, hh, Subgroup.coe_mul, MulAut.mul_apply]
    rw [hw _ (Subgroup.mem_subgroupOf.mp h.2)]
  set N := ∏ q, φ q with hN
  have hNfix : N ∈ fixV F := by
    intro x hx
    rw [hN, map_prod]
    have e : ∀ q, (x : MulAut W) (φ q) = φ ((⟨x, hx⟩ : ↥F) • q) := by
      intro q
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rw [show (⟨x, hx⟩ : ↥F) • (QuotientGroup.mk q.out : ↥F ⧸ S.subgroupOf F) =
        QuotientGroup.mk (⟨x, hx⟩ * q.out) from rfl, hφ]
      rfl
    simp_rw [e]
    exact Fintype.prod_equiv (MulAction.toPerm (⟨x, hx⟩ : ↥F)) _ _ fun q => rfl
  have hcomm : N * (w ^ Fintype.card (↥F ⧸ S.subgroupOf F))⁻¹ ∈ commV F := by
    have : N * (w ^ Fintype.card (↥F ⧸ S.subgroupOf F))⁻¹ = ∏ q, (φ q * w⁻¹) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, inv_pow]
    rw [this]
    refine Subgroup.prod_mem _ fun q _ => Subgroup.subset_closure ⟨_, (q.out).2, w, rfl⟩
  have hcard : Fintype.card (↥F ⧸ S.subgroupOf F) = S.relIndex F := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  obtain ⟨k, hk⟩ : Odd (S.relIndex F) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have hwk : w ^ Fintype.card (↥F ⧸ S.subgroupOf F) = w := by
    rw [hcard, hk, pow_succ, pow_mul, hW, one_pow, one_mul]
  rw [hwk] at hcomm
  have e : w = (N * w⁻¹)⁻¹ * N := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hcomm))
    (Subgroup.mem_sup_right hNfix)

end Transfer

section Realize

variable {V : Type*} [CommGroup V]

theorem fix_of_realizesVia_ch615 {D : FFModel} {H : Subgroup (MulAut V)} {U : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U ⊥ π) {S' R' : Subgroup D.Gam}
    (hmodel : ∀ m ∈ D.sec, (∀ γ ∈ S', D.act γ m * m⁻¹ ∈ D.ker) →
      ∀ γ ∈ R', D.act γ m * m⁻¹ ∈ D.ker)
    {w : V} (hwU : w ∈ U) (hw : ∀ γ ∈ S', ((π γ : ↥H) : MulAut V) w = w) :
    ∀ γ ∈ R', ((π γ : ↥H) : MulAut V) w = w := by
  obtain ⟨-, -, -, hHU, -, hsec, -, β, -, hβk, hβe⟩ := h
  obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective (β ⟨w, hwU⟩)
  have hmS : ∀ γ ∈ S', D.act γ (m' : D.Amb) * (m' : D.Amb)⁻¹ ∈ D.ker := by
    intro γ hγ
    have h1 := hβe γ ⟨w, hwU⟩ m' (hHU (π γ) w hwU) (hsec γ _ m'.2) hm'.symm
    have h2 : (⟨((π γ : ↥H) : MulAut V) w, hHU (π γ) w hwU⟩ : ↥U) = ⟨w, hwU⟩ :=
      Subtype.ext (hw γ hγ)
    rw [h2, ← hm', QuotientGroup.eq] at h1
    have h3 : (m' : D.Amb)⁻¹ * D.act γ (m' : D.Amb) ∈ D.ker := Subgroup.mem_subgroupOf.mp h1
    rwa [mul_comm] at h3
  intro γ hγ
  have hR := hmodel _ m'.2 hmS γ hγ
  have h1 := hβe γ ⟨w, hwU⟩ m' (hHU (π γ) w hwU) (hsec γ _ m'.2) hm'.symm
  have h2 : β ⟨((π γ : ↥H) : MulAut V) w, hHU (π γ) w hwU⟩ = β ⟨w, hwU⟩ := by
    rw [h1, ← hm', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h5 := D.ker.inv_mem hR
    rw [mul_inv_rev, inv_inv, mul_comm] at h5
    simpa using h5
  have h3 : β (⟨((π γ : ↥H) : MulAut V) w, hHU (π γ) w hwU⟩ * (⟨w, hwU⟩ : ↥U)⁻¹) = 1 := by
    rw [map_mul, map_inv, h2, mul_inv_cancel]
  have h4 := (hβk _).mp h3
  rw [Subgroup.mem_bot] at h4
  simpa [mul_inv_eq_one] using h4

end Realize

section DirectSum

variable {V : Type*} [CommGroup V]

theorem exists_prod_of_mem_iSup_ch615 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {I : ι → Subgroup V} {w : V} (hw : w ∈ ⨆ i, I i) :
    ∃ f : ι → V, (∀ i, f i ∈ I i) ∧ ∏ i, f i = w := by
  let P : Subgroup V :=
    { carrier := {w | ∃ f : ι → V, (∀ i, f i ∈ I i) ∧ ∏ i, f i = w}
      mul_mem' := by
        rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
        exact ⟨f * g, fun i => (I i).mul_mem (hf i) (hg i), by
          rw [← Finset.prod_mul_distrib]; rfl⟩
      one_mem' := ⟨1, fun i => (I i).one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨f, hf, rfl⟩
        exact ⟨f⁻¹, fun i => (I i).inv_mem (hf i), by
          rw [← Finset.prod_inv_distrib]; rfl⟩ }
  have hle : (⨆ i, I i) ≤ P := iSup_le fun i v hv =>
    ⟨Pi.mulSingle i v, fun j => by
      by_cases hj : j = i
      · subst hj; simpa using hv
      · rw [Pi.mulSingle_eq_of_ne hj]; exact (I j).one_mem, by
      rw [Finset.prod_pi_mulSingle']; simp⟩
  exact hle hw

theorem fix_of_iSup_ch615 {ι : Type*} [Fintype ι] [DecidableEq ι] {I : ι → Subgroup V}
    (hind : ∀ i, I i ⊓ (⨆ (j : ι) (_ : j ≠ i), I j) = ⊥) {S R : Subgroup (MulAut V)}
    (hSI : ∀ s ∈ S, ∀ i, ∀ v ∈ I i, s v ∈ I i)
    (hfix : ∀ i, ∀ v ∈ I i, (∀ s ∈ S, s v = v) → ∀ x ∈ R, x v = v) {w : V}
    (hw : w ∈ ⨆ i, I i) (hwS : ∀ s ∈ S, s w = w) : ∀ x ∈ R, x w = w := by
  obtain ⟨f, hf, rfl⟩ := exists_prod_of_mem_iSup_ch615 hw
  have hfS : ∀ i, ∀ s ∈ S, s (f i) = f i := by
    intro i s hs
    have h1 : ∏ j, s (f j) * (f j)⁻¹ = 1 := by
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← map_prod, hwS s hs,
        mul_inv_cancel]
    have hmem : s (f i) * (f i)⁻¹ ∈ I i ⊓ (⨆ (j : ι) (_ : j ≠ i), I j) := by
      refine ⟨(I i).mul_mem (hSI s hs i _ (hf i)) ((I i).inv_mem (hf i)), ?_⟩
      have h2 : s (f i) * (f i)⁻¹ = (∏ j ∈ Finset.univ.erase i, s (f j) * (f j)⁻¹)⁻¹ := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at h1
        exact eq_inv_of_mul_eq_one_left h1
      rw [h2]
      refine Subgroup.inv_mem _ (Subgroup.prod_mem _ fun j hj => ?_)
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      exact (le_iSup₂ (f := fun (j : ι) (_ : j ≠ i) => I j) j hji)
        ((I j).mul_mem (hSI s hs j _ (hf j)) ((I j).inv_mem (hf j)))
    rw [hind i, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  intro x hx
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => hfix i _ (hf i) (hfS i) x hx

end DirectSum

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem autI_le_sup_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    autI hU (borelL T L ⊔ H) ≤ (autI hU D ⊔ autI hU T) ⊔ autI hU (oTwoUpper H) := by
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hBN : borelL T L ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_sup_left.trans hXN
  have hHN : H ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_sup_right.trans hXN
  have hDN : D ≤ Subgroup.normalizer (UX615 T L H : Set G) := hD.1.trans hBN
  have hTN : T ≤ Subgroup.normalizer (UX615 T L H : Set G) := c.hH.1.1.trans hHN
  have hKN : oTwoUpper H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    (oTwoUpper_le H).trans hHN
  have hTLN : T ⊓ L ≤ Subgroup.normalizer (UX615 T L H : Set G) := inf_le_left.trans hTN
  have hB : D ⊔ (T ⊓ L) = borelL T L := c.hyp.toHyp5_0_1.borelL_eq_sup hD
  have hH : T ⊔ oTwoUpper H = H := by
    have hsup : T ⊔ twoResidual H = H := sup_twoResidual_eq c.toCx615.isSylowTwoOf
    rwa [twoResidual_eq_oTwoUpper'] at hsup
  rw [autI_sup hU hBN hHN]
  refine sup_le ?_ ?_
  · calc autI hU (borelL T L) = autI hU (D ⊔ (T ⊓ L)) := by rw [hB]
      _ = autI hU D ⊔ autI hU (T ⊓ L) := autI_sup hU hDN hTLN
      _ ≤ _ := sup_le (le_sup_left.trans le_sup_left)
          ((autI_mono hU inf_le_left).trans (le_sup_right.trans le_sup_left))
  · calc autI hU H = autI hU (T ⊔ oTwoUpper H) := by rw [hH]
      _ = autI hU T ⊔ autI hU (oTwoUpper H) := autI_sup hU hTN hKN
      _ ≤ _ := sup_le (le_sup_right.trans le_sup_left) le_sup_right

omit [Finite G] in
theorem mem_normalizer_sup_ch615 {Γ : Type*} [Group Γ] [Finite Γ] {A B : Subgroup Γ} {t : Γ}
    (hA : t ∈ Subgroup.normalizer (A : Set Γ)) (hB : t ∈ Subgroup.normalizer (B : Set Γ)) :
    t ∈ Subgroup.normalizer ((A ⊔ B : Subgroup Γ) : Set Γ) := by
  refine mem_normalizer_of_conj_mem_l32_ch615 fun y hy => ?_
  have hle : (A ⊔ B).map (MulAut.conj t).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hA a).mp ha
    · rintro _ ⟨b, hb, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hB b).mp hb
  exact hle ⟨y, hy, rfl⟩

theorem le_sup_overgroups_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hFX : F ≤ autI hU (borelL T L ⊔ H))
    (hXF : autI hU (borelL T L ⊔ H) ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hdl : DLemmaFacts_ch615 F) (hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1)
    (hKF : autI hU (oTwoUpper H) ≤ F) :
    F ≤ (autI hU (oTwoUpper H) ⊔ (autI hU T ⊓ F)) ⊔ (autI hU (borelL T L ⊔ T) ⊓ F) := by
  classical
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hS := c.isSylowTwoOf_inf_ch615 hU hFX hXF
  obtain ⟨-, hout, hNS, hself⟩ := hdl
  set PK := autI hU (oTwoUpper H) ⊔ (autI hU T ⊓ F) with hPK
  set PD := autI hU (borelL T L ⊔ T) ⊓ F with hPD
  set X := autI hU (borelL T L ⊔ H) with hX
  set C := X ⊓ Subgroup.centralizer (F : Set (MulAut (IntMod (UX615 T L H) hU))) with hC
  have hDY : autI hU D ≤ autI hU (borelL T L ⊔ T) := autI_mono hU (hD.1.trans le_sup_left)
  have hTY : autI hU T ≤ autI hU (borelL T L ⊔ T) := autI_mono hU le_sup_right
  have hYX : autI hU (borelL T L ⊔ T) ≤ X :=
    autI_mono hU (sup_le le_sup_left (c.hH.1.1.trans le_sup_right))
  have hTX : autI hU T ≤ X := hTY.trans hYX
  have hDsodd : ∀ d ∈ autI hU D, Odd (orderOf d) := by
    have hodd : Odd (Nat.card (autI hU D)) := by
      rw [(c.autI_hall_ch615 hU hD).2, ← (c.hall_ch615 hD).2]
      exact hD.2.1
    exact fun d hd => Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hd)
  have hYF : PK ⊔ PD ≤ F := sup_le (sup_le hKF inf_le_right) inf_le_right
  have hXle : X ≤ (PK ⊔ PD) ⊔ (C ⊔ autI hU T) := by
    refine (c.autI_le_sup_ch615 hU hD).trans (sup_le (sup_le ?_ ?_) ?_)
    · intro δ hδ
      obtain ⟨g, hgF, hδg, hg⟩ := exists_inner_of_odd_ch615 hout hZ hS.isPGroup hS.le
        (hNS _ hS) (hself _ hS) (inf_le_left.trans hTY) (c.isSolvable_autI_ch615 hU)
        (hDY hδ) (hXF (hYX (hDY hδ))) (hDsodd δ hδ)
      have hgY : g ∈ PK ⊔ PD := by
        rcases hg with rfl | hgY
        · exact Subgroup.one_mem _
        · exact Subgroup.mem_sup_right ⟨hgY, hgF⟩
      have hc : g⁻¹ * δ ∈ C := ⟨X.mul_mem (X.inv_mem (hFX hgF)) (hYX (hDY hδ)),
        Subgroup.mem_centralizer_iff.mpr fun x hx => by
          have := hδg x hx
          calc x * (g⁻¹ * δ) = g⁻¹ * (g * x * g⁻¹) * δ := by group
            _ = g⁻¹ * (δ * x * δ⁻¹) * δ := by rw [this]
            _ = g⁻¹ * δ * x := by group⟩
      have e : δ = g * (g⁻¹ * δ) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgY)
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left hc))
    · exact le_sup_right.trans le_sup_right
    · exact (le_sup_left.trans le_sup_left : autI hU (oTwoUpper H) ≤ PK ⊔ PD).trans le_sup_left
  have hWY : C ⊔ autI hU T ≤
      Subgroup.normalizer ((PK ⊔ PD : Subgroup _) : Set (MulAut (IntMod (UX615 T L H) hU))) := by
    refine sup_le (fun x hx => mem_normalizer_of_conj_mem_l32_ch615 fun y hy => ?_)
      (fun t ht => mem_normalizer_sup_ch615 (mem_normalizer_sup_ch615
        (c.autI_le_normalizer_oTwoUpper_ch615 hU ht) ?_) ?_)
    · have h1 := Subgroup.mem_centralizer_iff.mp hx.2 y (hYF hy)
      rw [← h1, mul_inv_cancel_right]
      exact hy
    · refine mem_normalizer_of_conj_mem_l32_ch615 fun y hy => ⟨?_, ?_⟩
      · exact (autI hU T).mul_mem ((autI hU T).mul_mem ht hy.1) ((autI hU T).inv_mem ht)
      · exact (Subgroup.mem_normalizer_iff.mp (hXF (hTX ht)) y).mp hy.2
    · refine mem_normalizer_of_conj_mem_l32_ch615 fun y hy => ⟨?_, ?_⟩
      · exact (autI hU _).mul_mem ((autI hU _).mul_mem (hTY ht) hy.1) ((autI hU _).inv_mem (hTY ht))
      · exact (Subgroup.mem_normalizer_iff.mp (hXF (hTX ht)) y).mp hy.2
  have hP := isPGroup_inf_sup_ch615 hXF hTX (c.isPGroup_autI_ch615 hU) hZ
  have hle : autI hU T ⊓ F ≤ F ⊓ (C ⊔ autI hU T) := fun x hx =>
    ⟨hx.2, Subgroup.mem_sup_right hx.1⟩
  have heq : autI hU T ⊓ F = F ⊓ (C ⊔ autI hU T) := Subgroup.eq_of_le_of_card_ge hle (by
    rw [hS.card_eq]
    exact card_le_twoPart inf_le_left hP)
  intro l hl
  have hlY : l ∈ (((PK ⊔ PD) ⊔ (C ⊔ autI hU T) : Subgroup _) : Set (MulAut _)) :=
    hXle (hFX hl)
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hWY] at hlY
  obtain ⟨y, hy, w, hw, rfl⟩ := Set.mem_mul.mp hlY
  have hwF : w ∈ F := by
    have := F.mul_mem (F.inv_mem (hYF hy)) hl
    simpa using this
  have hwS : w ∈ autI hU T ⊓ F := heq ▸ ⟨hwF, hw⟩
  exact Subgroup.mul_mem _ hy (Subgroup.mem_sup_left (Subgroup.mem_sup_right hwS))

end Cx615C

end CFSG.Quasithin.H13
