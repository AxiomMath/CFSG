module

public import CFSG.Quasithin.Background.F918P5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Transfer

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂] {P Q : Type*} [CommGroup P] [CommGroup Q]
  [MulDistribMulAction G₁ P] [MulDistribMulAction G₂ Q]

structure ActCompat (ι : P →* Q) (X₁ : Subgroup G₁) (X₂ : Subgroup G₂) : Prop where
  fwd : ∀ b ∈ X₁, ∃ a ∈ X₂, ∀ p, ι (b • p) = a • ι p
  bwd : ∀ a ∈ X₂, ∃ b ∈ X₁, ∀ p, ι (b • p) = a • ι p

namespace ActCompat

variable {ι : P →* Q} {X₁ : Subgroup G₁} {X₂ : Subgroup G₂}

theorem isInv_map_iff (hι : Function.Injective ι) (hX : ActCompat ι X₁ X₂) (L : Subgroup P) :
    XMod.IsInv ↥X₂ (L.map ι) ↔ XMod.IsInv ↥X₁ L := by
  constructor
  · intro h b l hl
    obtain ⟨a, ha, hab⟩ := hX.fwd b b.2
    obtain ⟨l', hl', hll'⟩ := Subgroup.mem_map.1 (h ⟨a, ha⟩ (ι l) (Subgroup.mem_map_of_mem _ hl))
    have h1 : ι (b • l) = ι l' := (hab l).trans hll'.symm
    rw [hι h1]
    exact hl'
  · intro h a q hq
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hq
    obtain ⟨b, hb, hba⟩ := hX.bwd a a.2
    have h1 : a • ι l = ι ((⟨b, hb⟩ : ↥X₁) • l) := (hba l).symm
    rw [h1]
    exact Subgroup.mem_map_of_mem _ (h ⟨b, hb⟩ l hl)

theorem fixed_map_eq (hι : Function.Injective ι) (hX : ActCompat ι X₁ X₂) (L : Subgroup P) :
    XMod.fixed ↥X₂ (L.map ι) = (XMod.fixed ↥X₁ L).map ι := by
  ext q
  constructor
  · rintro ⟨hq, hfix⟩
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hq
    refine ⟨l, ⟨hl, fun b => ?_⟩, rfl⟩
    obtain ⟨a, ha, hab⟩ := hX.fwd b b.2
    apply hι
    have h1 : ι (b • l) = ι l := (hab l).trans (hfix ⟨a, ha⟩)
    exact h1
  · rintro ⟨l, ⟨hl, hfix⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ hl, fun a => ?_⟩
    obtain ⟨b, hb, hba⟩ := hX.bwd a a.2
    have h1 : a • ι l = ι ((⟨b, hb⟩ : ↥X₁) • l) := (hba l).symm
    rw [h1, hfix ⟨b, hb⟩]

theorem commOf_map_eq (hX : ActCompat ι X₁ X₂) (L : Subgroup P) :
    XMod.commOf ↥X₂ (L.map ι) = (XMod.commOf ↥X₁ L).map ι := by
  unfold XMod.commOf
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨a, q, hq, rfl⟩
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hq
    obtain ⟨b, hb, hba⟩ := hX.bwd a a.2
    refine ⟨_, ⟨⟨b, hb⟩, l, hl, rfl⟩, ?_⟩
    simp only [map_mul, map_inv]
    have := hba l
    show ι (b • l) * (ι l)⁻¹ = (a • ι l) * (ι l)⁻¹
    rw [this]
    rfl
  · rintro ⟨_, ⟨b, l, hl, rfl⟩, rfl⟩
    obtain ⟨a, ha, hab⟩ := hX.fwd b b.2
    refine ⟨⟨a, ha⟩, ι l, Subgroup.mem_map_of_mem _ hl, ?_⟩
    simp only [map_mul, map_inv]
    have := hab l
    exact congrArg (· * (ι l)⁻¹) this

theorem isIrrSec_map_iff (hι : Function.Injective ι) (hX : ActCompat ι X₁ X₂)
    (C L : Subgroup P) :
    XMod.IsIrrSec ↥X₂ (C.map ι) (L.map ι) ↔ XMod.IsIrrSec ↥X₁ C L := by
  unfold XMod.IsIrrSec
  rw [Subgroup.map_lt_map_iff_of_injective hι]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h J hJ hCJ hJL
    have hJ' : XMod.IsInv ↥X₂ (J.map ι) := (hX.isInv_map_iff hι J).2 hJ
    rcases h (J.map ι) hJ' (Subgroup.map_mono hCJ) (Subgroup.map_mono hJL) with h1 | h1
    · exact Or.inl (Subgroup.map_injective hι h1)
    · exact Or.inr (Subgroup.map_injective hι h1)
  · intro h J' hJ' hCJ' hJL'
    have hrange : J' ≤ ι.range := hJL'.trans (Subgroup.map_le_range ι L)
    have hJJ : (J'.comap ι).map ι = J' := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.2 hrange
    have hJinv : XMod.IsInv ↥X₁ (J'.comap ι) := by
      intro b j hj
      obtain ⟨a, ha, hab⟩ := hX.fwd b b.2
      rw [Subgroup.mem_comap] at hj ⊢
      have h1 : ι (b • j) = (⟨a, ha⟩ : ↥X₂) • ι j := hab j
      rw [h1]
      exact hJ' ⟨a, ha⟩ _ hj
    have hCJ : C ≤ J'.comap ι := fun c hc => hCJ' (Subgroup.mem_map_of_mem _ hc)
    have hJL : J'.comap ι ≤ L := by
      intro j hj
      obtain ⟨l, hl, hlj⟩ := Subgroup.mem_map.1 (hJL' (Subgroup.mem_comap.1 hj))
      rw [← hι hlj]
      exact hl
    rcases h (J'.comap ι) hJinv hCJ hJL with h1 | h1
    · left
      rw [← hJJ, h1]
    · right
      rw [← hJJ, h1]

theorem isIrrPlus_map_iff (hι : Function.Injective ι) (hX : ActCompat ι X₁ X₂) (I : Subgroup P) :
    XMod.IsIrrPlus ↥X₂ (I.map ι) ↔ XMod.IsIrrPlus ↥X₁ I := by
  unfold XMod.IsIrrPlus
  rw [hX.isInv_map_iff hι, hX.commOf_map_eq, hX.fixed_map_eq hι, hX.isIrrSec_map_iff hι,
    Subgroup.map_injective hι |>.eq_iff]

end ActCompat

end Transfer

section IsoTransfer

variable {A₁ A₂ : Type*} [Group A₁] [Group A₂] {Q₁ Q₂ : Type*} [CommGroup Q₁] [CommGroup Q₂]
  [MulDistribMulAction A₁ Q₁] [MulDistribMulAction A₂ Q₂]

theorem exists_equivMap_of_injOn (θ : Q₁ →* Q₂) {S L : Subgroup Q₁}
    (hinj : ∀ x ∈ S, ∀ y ∈ S, θ x = θ y → x = y) (hL : L ≤ S) :
    ∃ e : ↥L ≃* ↥(L.map θ), ∀ x : ↥L, ((e x : ↥(L.map θ)) : Q₂) = θ (x : Q₁) := by
  refine ⟨MulEquiv.ofBijective (θ.subgroupMap L) ⟨fun x y hxy => ?_, θ.subgroupMap_surjective L⟩,
    fun x => rfl⟩
  apply Subtype.ext
  exact hinj _ (hL x.2) _ (hL y.2) (congrArg Subtype.val hxy)

theorem iso_map_of_injOn (θ : Q₁ →* Q₂) (hθ : ∀ a₂ : A₂, ∃ a₁ : A₁, ∀ x, θ (a₁ • x) = a₂ • θ x)
    {S : Subgroup Q₁} (hS : XMod.IsInv A₁ S) (hinj : ∀ x ∈ S, θ x = 1 → x = 1)
    {L₁ L₂ : Subgroup Q₁} (h₁ : L₁ ≤ S) (h₂ : L₂ ≤ S) (h : XMod.Iso A₁ L₁ L₂) :
    XMod.Iso A₂ (L₁.map θ) (L₂.map θ) := by
  obtain ⟨φ, hφ⟩ := h
  have hinj' : ∀ x ∈ S, ∀ y ∈ S, θ x = θ y → x = y := by
    intro x hx y hy hxy
    have : x * y⁻¹ = 1 := hinj _ (S.mul_mem hx (S.inv_mem hy))
      (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    exact mul_inv_eq_one.1 this
  obtain ⟨e₁, he₁⟩ := exists_equivMap_of_injOn θ hinj' h₁
  obtain ⟨e₂, he₂⟩ := exists_equivMap_of_injOn θ hinj' h₂
  refine ⟨e₁.symm.trans (φ.trans e₂), fun a l l' hll' => ?_⟩
  have hx : θ ((e₁.symm l : ↥L₁) : Q₁) = (l : Q₂) := by
    rw [← he₁, MulEquiv.apply_symm_apply]
  have hx' : θ ((e₁.symm l' : ↥L₁) : Q₁) = (l' : Q₂) := by
    rw [← he₁, MulEquiv.apply_symm_apply]
  obtain ⟨a₁, ha₁⟩ := hθ a
  have h1 : a₁ • ((e₁.symm l : ↥L₁) : Q₁) = ((e₁.symm l' : ↥L₁) : Q₁) := by
    apply hinj' _ (hS a₁ _ (h₁ (e₁.symm l).2)) _ (h₁ (e₁.symm l').2)
    rw [ha₁, hx, hx', hll']
  have h2 := hφ a₁ (e₁.symm l) (e₁.symm l') h1
  show a • ((e₂ (φ (e₁.symm l)) : ↥(L₂.map θ)) : Q₂) = ((e₂ (φ (e₁.symm l')) : ↥(L₂.map θ)) : Q₂)
  rw [he₂, he₂, ← ha₁, h2]

end IsoTransfer

section IrrPlusTransfer

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂] {P Q : Type*} [CommGroup P] [CommGroup Q]
  [MulDistribMulAction G₁ P] [MulDistribMulAction G₂ Q]
  {ι : P →* Q} {X₁ : Subgroup G₁} {X₂ : Subgroup G₂} {Wp : Subgroup P} {Wq : Subgroup Q}

theorem ActCompat.iso_tilde_map (hι : Function.Injective ι) (hX : ActCompat ι X₁ X₂)
    (hWpq : ∀ w ∈ Wp, ι w ∈ Wq) (hWinv : IsModInv X₁ Wp)
    {J₁ J₂ : Subgroup P} (h₁ : J₁ ≤ Wp) (h₂ : J₂ ≤ Wp)
    (h : XMod.Iso ↥X₁ (tilde X₁ Wp J₁) (tilde X₁ Wp J₂)) :
    XMod.Iso ↥X₂ (tilde X₂ Wq (J₁.map ι)) (tilde X₂ Wq (J₂.map ι)) := by
  have hle : modFix X₁ Wp ≤ (modFix X₂ Wq).comap ι := by
    intro c hc
    rw [Subgroup.mem_comap]
    refine ⟨hWpq c hc.1, fun a => ?_⟩
    obtain ⟨b, hb, hba⟩ := hX.bwd a a.2
    have h1 : a • ι c = ι ((⟨b, hb⟩ : ↥X₁) • c) := (hba c).symm
    rw [h1, hc.2 ⟨b, hb⟩]
  let θ : (P ⧸ modFix X₁ Wp) →* (Q ⧸ modFix X₂ Wq) := QuotientGroup.map _ _ ι hle
  have hθmk : ∀ p : P, θ (QuotientGroup.mk p) = QuotientGroup.mk (ι p) := fun p => rfl
  have hθact : ∀ a₂ : ↥X₂, ∃ a₁ : ↥X₁, ∀ x, θ (a₁ • x) = a₂ • θ x := by
    intro a
    obtain ⟨b, hb, hba⟩ := hX.bwd a a.2
    refine ⟨⟨b, hb⟩, fun x => ?_⟩
    induction x using QuotientGroup.induction_on with
    | H p =>
      rw [XMod.smul_quotMk, hθmk, hθmk, XMod.smul_quotMk]
      exact congrArg QuotientGroup.mk (hba p)
  have hS : XMod.IsInv ↥X₁ (tilde X₁ Wp Wp) := isInv_tilde hWinv
  have hinj : ∀ x ∈ tilde X₁ Wp Wp, θ x = 1 → x = 1 := by
    intro x hx h1
    obtain ⟨w, hw, rfl⟩ := mem_tilde_iff.1 hx
    rw [hθmk, QuotientGroup.eq_one_iff] at h1
    have : w ∈ modFix X₁ Wp := by
      refine ⟨hw, fun b => ?_⟩
      obtain ⟨a, ha, hab⟩ := hX.fwd b b.2
      apply hι
      have h2 : ι (b • w) = ι w := (hab w).trans (h1.2 ⟨a, ha⟩)
      exact h2
    exact (QuotientGroup.eq_one_iff w).2 this
  have hmap : ∀ J : Subgroup P, tilde X₂ Wq (J.map ι) = (tilde X₁ Wp J).map θ := by
    intro J
    ext q
    constructor
    · intro hq
      obtain ⟨v, hv, rfl⟩ := mem_tilde_iff.1 hq
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hv
      exact ⟨QuotientGroup.mk j, mem_tilde_iff.2 ⟨j, hj, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨j, hj, rfl⟩ := mem_tilde_iff.1 hx
      exact mem_tilde_iff.2 ⟨ι j, Subgroup.mem_map_of_mem _ hj, rfl⟩
  rw [hmap, hmap]
  exact iso_map_of_injOn θ hθact hS hinj (tilde_mono h₁) (tilde_mono h₂) h

theorem ActCompat.mem_irrPlusOn_of_map (hι : Function.Injective ι) (hX : ActCompat ι X₁ X₂)
    {T₁ : Subgroup G₁} {T₂ : Subgroup G₂} (hT : ActCompat ι T₁ T₂)
    (hTX₁ : T₁ ≤ Subgroup.normalizer (X₁ : Set G₁))
    (hTX₂ : T₂ ≤ Subgroup.normalizer (X₂ : Set G₂))
    (hWq : ∀ t ∈ T₂, ∀ w ∈ Wq, t • w ∈ Wq) {I : Subgroup P}
    (hI : I.map ι ∈ IrrPlusOn X₂ Wq T₂) : I ∈ IrrPlusOn X₁ (⨆ y ∈ T₁, y • I) T₁ := by
  have hIirr : XMod.IsIrrPlus ↥X₁ I := (hX.isIrrPlus_map_iff hι I).1 hI.1.2
  have hIinv : IsModInv X₁ I := hIirr.1
  have hWpT : ∀ t ∈ T₁, ∀ w ∈ (⨆ y ∈ T₁, y • I), t • w ∈ (⨆ y ∈ T₁, y • I) :=
    fun t ht w hw => smul_mem_biSup_smul ht hw
  have hIWp : I ≤ ⨆ y ∈ T₁, y • I := by
    have := le_biSup_smul T₁ I T₁.one_mem
    rwa [one_smul] at this
  have hWinv : IsModInv X₁ (⨆ y ∈ T₁, y • I) :=
    XMod.isInv_iSup fun y => XMod.isInv_iSup fun hy => isModInv_smul (hTX₁ hy) hIinv
  have hWpq : ∀ w ∈ (⨆ y ∈ T₁, y • I), ι w ∈ Wq := by
    have hle : (⨆ y ∈ T₁, y • I) ≤ Wq.comap ι := by
      refine iSup₂_le fun y hy x hx => ?_
      obtain ⟨i, hi, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists x y I).1 hx
      obtain ⟨y', hy', hyy'⟩ := hT.fwd y hy
      rw [Subgroup.mem_comap, hyy' i]
      exact hWq y' hy' _ (hI.1.1 (Subgroup.mem_map_of_mem _ hi))
    exact fun w hw => hle hw
  refine (forall_smul_eq_iff_mem_irrPlusOn hTX₁ hWpT ⟨hIWp, hIirr⟩).1 ?_
  rintro t ⟨ht, hiso⟩
  obtain ⟨t', ht', hcompat⟩ := hT.fwd t ht
  have hclass := (forall_smul_eq_iff_mem_irrPlusOn hTX₂ hWq hI.1).2 hI
  have e : t' • I.map ι = (t • I).map ι := by
    ext q
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.1 hs
      exact ⟨t • i, Subgroup.smul_mem_pointwise_smul i t I hi, hcompat i⟩
    · intro hq
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
      obtain ⟨i, hi, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists x t I).1 hx
      exact ⟨ι i, Subgroup.mem_map_of_mem _ hi, (hcompat i).symm⟩
  have hiso' : XMod.Iso ↥X₂ (tilde X₂ Wq (t' • I.map ι)) (tilde X₂ Wq (I.map ι)) := by
    rw [e]
    exact hX.iso_tilde_map hι hWpq hWinv (le_biSup_smul T₁ I ht) hIWp hiso
  have h1 := hclass t' ⟨ht', hiso'⟩
  rw [e] at h1
  exact Subgroup.map_injective hι h1

end IrrPlusTransfer


section Ambient

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] {T V L V₁ Vp H K I : Subgroup G}

theorem autIH_T_le_normalizer (h : HypF918 T V L V₁ Vp H K) (I : Subgroup G) :
    autIH V₁ I H T ≤ Subgroup.normalizer
      ((autIH V₁ I H (conjClosure K T) : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure I H)))) :
        Set (MulAut ↥(tildeOf V₁ (conjClosure I H)))) := by
  rw [autIH_eq_map h h.T_le_H, autIH_eq_map h h.K₀_le_H]
  exact (Subgroup.map_mono (by rw [Subgroup.subgroupOf_self]; exact le_top)).trans
    (map_le_normalizer_map_of_le_normalizer _ h.K₀_le_H h.K₀_normal)

@[expose] noncomputable def inclEU (V₁ : Subgroup G) (hIU : I ≤ conjClosure Vp H) :
    ↥(tildeOf V₁ (conjClosure I H)) →* ↥(tildeOf V₁ (conjClosure Vp H)) :=
  Subgroup.inclusion (secImg_mono (conjClosure_le_conjClosure_U hIU le_rfl))

theorem inclEU_injective (hIU : I ≤ conjClosure Vp H) : Function.Injective (inclEU V₁ hIU) :=
  Subgroup.inclusion_injective _

theorem inclEU_actH (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (x : ↥H)
    (e : ↥(tildeOf V₁ (conjClosure I H))) :
    inclEU V₁ hIU (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x e) =
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) x (inclEU V₁ hIU e) := by
  apply Subtype.ext
  exact (actH_apply_coe h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x e).trans
    (actH_apply_coe h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) x (inclEU V₁ hIU e)).symm

theorem actCompat_autIH (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)))] {X : Subgroup G} (hXH : X ≤ H) :
    ActCompat (inclEU V₁ hIU) (autIH V₁ I H X) (autIH V₁ Vp H X) := by
  rw [autIH_eq_map h hXH, autIH_eq_map h hXH]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, fun p => inclEU_actH h hIU x p⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, fun p => inclEU_actH h hIU x p⟩

theorem map_inclEU_subM (hIU : I ≤ conjClosure Vp H) :
    (subM V₁ (conjClosure I H) I).map (inclEU V₁ hIU) = subM V₁ (conjClosure Vp H) I := by
  ext u
  constructor
  · rintro ⟨e, he, rfl⟩
    exact he
  · intro hu
    exact ⟨⟨(u : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁),
      secImg_mono (le_conjClosure I H) (mem_subM_iff.1 hu)⟩, hu, rfl⟩

theorem orbSup_eq_biSup_smul {W : Type} [CommGroup W] (T : Subgroup (MulAut W)) (V : Subgroup W) :
    orbSup T V = ⨆ y ∈ T, y • V := by
  unfold orbSup
  refine iSup_congr fun y => iSup_congr fun _ => ?_
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  exact ⟨fun ⟨s, hs, hx⟩ => ⟨s, hs, hx⟩, fun ⟨s, hs, hx⟩ => ⟨s, hs, hx⟩⟩

end Ambient

section Final

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

@[expose] noncomputable def IsIrrPlusTildeU (h : HypF918 T V L V₁ Vp H K) (I : Subgroup G)
    (W : Subgroup ↥(tildeOf V₁ (conjClosure Vp H))) : Prop :=
  haveI := factElem h (le_conjClosure Vp H)
  subM V₁ (conjClosure Vp H) I ∈
    IrrPlusOn (autIH V₁ Vp H (conjClosure K T)) W (autIH V₁ Vp H T)

theorem isIrrPlusTildeT_of_ambient (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (W : Subgroup ↥(tildeOf V₁ (conjClosure Vp H)))
    (hW : ∀ t ∈ autIH V₁ Vp H T, ∀ w ∈ W, t w ∈ W) (hirr : IsIrrPlusTildeU h I W) :
    IsIrrPlusTildeT h hIU := by
  have := factElem h hIU
  have := factElem h (le_conjClosure Vp H)
  have hirr' : (subM V₁ (conjClosure I H) I).map (inclEU V₁ hIU) ∈
      IrrPlusOn (autIH V₁ Vp H (conjClosure K T)) W (autIH V₁ Vp H T) := by
    rw [map_inclEU_subM]
    exact hirr
  have key := (actCompat_autIH h hIU h.K₀_le_H).mem_irrPlusOn_of_map (inclEU_injective hIU)
    (actCompat_autIH h hIU h.T_le_H) (autIH_T_le_normalizer h I) (autIH_T_le_normalizer h Vp) hW
    hirr'
  show subM V₁ (conjClosure I H) I ∈ IrrPlusOn _ (orbSup _ _) _
  rw [orbSup_eq_biSup_smul]
  exact key

theorem F918_4' (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hK : conjClosure K T = K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (W : Subgroup ↥(tildeOf V₁ (conjClosure Vp H)))
    (hW : ∀ t ∈ autIH V₁ Vp H T, ∀ w ∈ W, t w ∈ W) (hirr : IsIrrPlusTildeU h I W)
    (h310 : D310) (h391 : D391) (hI4 : Insp4) :
    FourList (↥(autIH V₁ Vp H K) ⧸ Subgroup.center ↥(autIH V₁ Vp H K)) ∧ F918Four h hIU :=
  F918_4 h hH hK hV₁I hIU (isIrrPlusTildeT_of_ambient h hIU W hW hirr) h310 h391 hI4

theorem F918_4_fine' (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hK : conjClosure K T = K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (W : Subgroup ↥(tildeOf V₁ (conjClosure Vp H)))
    (hW : ∀ t ∈ autIH V₁ Vp H T, ∀ w ∈ W, t w ∈ W) (hirr : IsIrrPlusTildeU h I W)
    (h310 : D310) (h391 : D391) (hI4 : Insp4) (hFine : F918Fine4) :
    FourListFine ↥(autIH V₁ Vp H K) ∧ F918Four h hIU :=
  F918_4_fine h hH hK hV₁I hIU (isIrrPlusTildeT_of_ambient h hIU W hW hirr) h310 h391 hI4 hFine

theorem F918_5'
    (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hK : conjClosure K T ≠ K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (W : Subgroup ↥(tildeOf V₁ (conjClosure Vp H)))
    (hW : ∀ t ∈ autIH V₁ Vp H T, ∀ w ∈ W, t w ∈ W) (hirr : IsIrrPlusTildeU h I W)
    (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) :
    FiveShape ↥(autIH V₁ Vp H K) ∧
      ∀ t (ht : t ∈ T), t ∉ Subgroup.normalizer (K : Set G) → F918Five h hIU ht :=
  F918_5 h hH hK hV₁I hIU (isIrrPlusTildeT_of_ambient h hIU W hW hirr) hD36 hD37 hD321 hI5 hA37
    hA38

theorem F918_5_inv'
    (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hK : conjClosure K T ≠ K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (W : Subgroup ↥(tildeOf V₁ (conjClosure Vp H)))
    (hW : ∀ t ∈ autIH V₁ Vp H T, ∀ w ∈ W, t w ∈ W) (hirr : IsIrrPlusTildeU h I W)
    (hinv : ∀ x ∈ H, x ∈ Subgroup.normalizer (K : Set G) → x ∈ Subgroup.normalizer (I : Set G))
    (hD36 : D36) (hD37 : D37) (hI5 : Insp5a) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) :
    FiveShape ↥(autIH V₁ Vp H K) ∧
      ∀ t (ht : t ∈ T), t ∉ Subgroup.normalizer (K : Set G) → F918FiveTop h hIU ht :=
  F918_5_inv h hH hK hV₁I hIU (isIrrPlusTildeT_of_ambient h hIU W hW hirr) hinv hD36 hD37 hI5 hA37
    hA38

end Final

end CFSG.Quasithin
