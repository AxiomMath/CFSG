module

public import CFSG.Quasithin.Vol2.Ch10Reselect.JGroup
public import CFSG.Quasithin.Vol2.Ch10Reselect.GLemma

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma homog_mem_conjugate {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

private lemma homog_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  constructor
  · rintro ⟨hhA, hhB⟩
    exact ⟨(hA h).mp hhA, (hB h).mp hhB⟩
  · rintro ⟨hgA, hgB⟩
    exact ⟨(hA h).mpr hgA, (hB h).mpr hgB⟩

private lemma homog_normalizer_of_comm {V K : Subgroup G} {a : G}
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hK : K ≤ V) (ha : a ∈ V) :
    a ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hc : ∀ h' ∈ V, a * h' * a⁻¹ = h' := fun h' hh' => by
    rw [hcomm a ha h' hh', mul_inv_cancel_right]
  constructor
  · intro hh
    rw [hc h (hK hh)]
    exact hh
  · intro hah
    have hhV : h ∈ V := by
      have key : a⁻¹ * (a * h * a⁻¹) * a = h := by group
      have h2 := V.mul_mem (V.mul_mem (V.inv_mem ha) (hK hah)) ha
      rwa [key] at h2
    rw [hc h hhV] at hah
    exact hah

private lemma homog_normalizer_centralizer {L0 : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L0 : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (L0 : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc s hs
    have hs' : g⁻¹ * s * g⁻¹⁻¹ ∈ L0 :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) s).mp hs
    rw [inv_inv] at hs'
    have h := hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h]
      _ = (g * c * g⁻¹) * s := by group
  · intro hd s hs
    have hs' : g * s * g⁻¹ ∈ L0 := (Subgroup.mem_normalizer_iff.mp hg s).mp hs
    have h := hd _ hs'
    calc s * c = g⁻¹ * ((g * s * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * s * g⁻¹)) * g := by rw [h]
      _ = c * s := by group

theorem commutator_mem_of_sectionIso {X C J' K : Subgroup G} (h : IsXSectionIso X C J' K) {x : G}
    (hx : x ∈ X) (hxJ' : x ∈ Subgroup.normalizer (J' : Set G))
    (hxK : ∀ k ∈ K, x * k * x⁻¹ = k) : ∀ j ∈ J', j⁻¹ * (x * j * x⁻¹) ∈ C := by
  obtain ⟨hnJ, _, e, he⟩ := h
  intro j hj
  have hxj : x * j * x⁻¹ ∈ J' := (Subgroup.mem_normalizer_iff.mp hxJ' j).mp hj
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective
    (e (QuotientGroup.mk (⟨j, hj⟩ : ↥J') : ↥J' ⧸ C.subgroupOf J'))
  have hkK : x * (k : G) * x⁻¹ = k := hxK k k.2
  have hkmem : x * (k : G) * x⁻¹ ∈ K := by rw [hkK]; exact k.2
  have h1 := he x hx ⟨j, hj⟩ k hxj hkmem hk.symm
  have hsub : (⟨x * (k : G) * x⁻¹, hkmem⟩ : ↥K) = k := Subtype.ext hkK
  rw [hsub] at h1
  have h2 : (QuotientGroup.mk (⟨x * j * x⁻¹, hxj⟩ : ↥J') : ↥J' ⧸ C.subgroupOf J') =
      QuotientGroup.mk (⟨j, hj⟩ : ↥J') :=
    e.injective (h1.trans hk)
  have h3 := QuotientGroup.eq.mp h2.symm
  have h4 := Subgroup.mem_subgroupOf.mp h3
  simpa using h4

theorem irrPlus_homog (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {T L I J : Subgroup G} (hJ : JData T L I J) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    [IsMulCommutative ↥(fsuVM T L I)] (hVR : fsuVM T L I ≤ reducedAggregate (L ⊔ T))
    (hmem : ∀ u ∈ fsuUL T L I,
      (∀ l ∈ L, l * u * l⁻¹ * u⁻¹ ∈
        fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) →
      u ∈ fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) :
    ∀ J' : Subgroup G,
      reducedAggregate (L ⊔ T) ⊓ Subgroup.centralizer (fsuL0 T L : Set G) ≤ J' →
      J' ≤ conjClosure J T ⊔ reducedAggregate (L ⊔ T) ⊓ Subgroup.centralizer (fsuL0 T L : Set G) →
      fsuL0 T L ≤ Subgroup.normalizer (J' : Set G) →
      IsXSectionIso (fsuL0 T L)
        (reducedAggregate (L ⊔ T) ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) J'
        (J ⊔ reducedAggregate (L ⊔ T) ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) →
      J' ≤ J ⊔ reducedAggregate (L ⊔ T) ⊓ Subgroup.centralizer (fsuL0 T L : Set G) := by
  intro J' _ hJ'V hJ'N hJ'iso
  intro j' hj'
  have hcomm : ∀ x ∈ fsuVM T L I, ∀ y ∈ fsuVM T L I, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : ↥(fsuVM T L I)) ⟨y, hy⟩)
  set R := reducedAggregate (L ⊔ T) with hR
  set L0 := fsuL0 T L with hL0
  set V := fsuVM T L I with hV
  set U := fsuUL T L I with hU
  set M := fsuM T L with hM
  set C := R ⊓ Subgroup.centralizer (L0 : Set G) with hC
  have hLT : L ⊔ T ≤ M := CFSG.Quasithin.Vol2.Ch10.SecA.sup_le_fsuM T L
  have hRLT : R ≤ L ⊔ T := Subgroup.map_subtype_le _
  have hRM : R ≤ M := hRLT.trans hLT
  have hVM : V ≤ M := hVR.trans hRM
  have hL0M : L0 ≤ M := Subgroup.le_normalizer
  have hLL0 : L ≤ L0 := CFSG.Quasithin.Vol2.Ch10.SecA.le_fsuL0 T L
  have hTM : T ≤ M := le_sup_right.trans hLT
  have hJV : J ≤ V := hJ.le_fsuVM
  have hJU : J ≤ U := hJ.le_U
  have hJtV : CFSG.conjugate J t ≤ V := hJ.conjugate_le_fsuVM ht
  have hV_eq : conjClosure J T = J ⊔ CFSG.conjugate J t := JData.fsuV_eq h37 h38 hJ ht htn
  have hJN : J ≤ Subgroup.normalizer (CFSG.conjugate J t : Set G) :=
    fun a ha => homog_normalizer_of_comm hcomm hJtV (hJV ha)
  have hVN : V ≤ Subgroup.normalizer (C : Set G) := fun v hv =>
    homog_normalizer_inf (Subgroup.le_normalizer (hVR hv)) (homog_normalizer_centralizer (hVM hv))
  have hH : conjClosure J T ≤ Subgroup.normalizer (C : Set G) := by
    rw [hV_eq]
    exact sup_le (hJV.trans hVN) (hJtV.trans hVN)
  obtain ⟨v, hv, c, hc, rfl⟩ := mem_sup_of_le_normalizer hH (hJ'V hj')
  rw [hV_eq] at hv
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_le_normalizer hJN hv
  obtain ⟨b₀, hb₀def⟩ : ∃ b₀ : G, b₀ = t * b * t⁻¹ := ⟨_, rfl⟩
  have hb_eq : b = t⁻¹ * b₀ * t := by rw [hb₀def]; group
  have hb₀J : b₀ ∈ J := by rw [hb₀def]; exact homog_mem_conjugate.mp hb
  have hb₀U : b₀ ∈ U := hJU hb₀J
  have hb₀V : b₀ ∈ V := hJV hb₀J
  have hbR : b ∈ R := hVR (hJtV hb)
  have htN : t ∈ Subgroup.normalizer ((Subgroup.centralizer (L0 : Set G) : Subgroup G) : Set G) :=
    homog_normalizer_centralizer (hTM ht)
  have hCsub : C ≤ Subgroup.centralizer (L0 : Set G) := inf_le_right
  have hbx : ∀ x ∈ CFSG.conjugate L t, b⁻¹ * (x * b * x⁻¹) ∈ C := by
    intro x hx
    have hxL0 : x ∈ L0 := CFSG.Quasithin.Vol2.Ch10.SecA.conjugate_le_fsuL0 ht hx
    have hxJ : ∀ j ∈ J, x * j = j * x := fun j hj =>
      (Subgroup.mem_centralizer_iff.mp ((hJ.hA t ht htn).2.2 (hJU hj))) x hx
    have hxC : ∀ c' ∈ C, x * c' = c' * x := fun c' hc' =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc').2) x hxL0
    have hKx : J ⊔ C ≤ Subgroup.centralizer ({x} : Set G) := by
      apply sup_le
      · intro j hj
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact hxJ j hj
      · intro c' hc'
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact hxC c' hc'
    have hxK : ∀ k ∈ J ⊔ C, x * k * x⁻¹ = k := by
      intro k hk
      have hxk := (Subgroup.mem_centralizer_iff.mp (hKx hk)) x (Set.mem_singleton x)
      rw [hxk, mul_inv_cancel_right]
    have hkey := commutator_mem_of_sectionIso hJ'iso hxL0 (hJ'N hxL0) hxK
    have h1 := hkey (a * b * c) hj'
    have hxa : x * a * x⁻¹ = a := by rw [hxJ a ha, mul_inv_cancel_right]
    have hxc : x * c * x⁻¹ = c := by rw [hxC c hc, mul_inv_cancel_right]
    have hconj_prod : x * (a * b * c) * x⁻¹ = a * (x * b * x⁻¹) * c := by
      calc x * (a * b * c) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) * (x * c * x⁻¹) := by group
        _ = a * (x * b * x⁻¹) * c := by rw [hxa, hxc]
    rw [hconj_prod] at h1
    have e : (a * b * c)⁻¹ * (a * (x * b * x⁻¹) * c) = c⁻¹ * (b⁻¹ * (x * b * x⁻¹)) * c := by
      group
    rw [e] at h1
    have h3 : b⁻¹ * (x * b * x⁻¹) = c * (c⁻¹ * (b⁻¹ * (x * b * x⁻¹)) * c) * c⁻¹ := by group
    rw [h3]
    exact C.mul_mem (C.mul_mem hc h1) (C.inv_mem hc)
  have hwC : ∀ y ∈ L, b₀⁻¹ * (y * b₀ * y⁻¹) ∈ Subgroup.centralizer (L0 : Set G) := by
    intro y hy
    have hxmem : t⁻¹ * y * t ∈ CFSG.conjugate L t := by
      rw [homog_mem_conjugate]
      have e : t * (t⁻¹ * y * t) * t⁻¹ = y := by group
      rw [e]
      exact hy
    have h1 := hbx (t⁻¹ * y * t) hxmem
    have e2 : b⁻¹ * (t⁻¹ * y * t * b * (t⁻¹ * y * t)⁻¹) =
        t⁻¹ * (b₀⁻¹ * (y * b₀ * y⁻¹)) * t := by
      rw [hb_eq]
      group
    rw [e2] at h1
    have h2 := hCsub h1
    have h3 : t⁻¹ * (b₀⁻¹ * (y * b₀ * y⁻¹)) * t⁻¹⁻¹ ∈ Subgroup.centralizer (L0 : Set G) := by
      rw [inv_inv]
      exact h2
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN)
      (b₀⁻¹ * (y * b₀ * y⁻¹))).mpr h3
  have hwZ : ∀ y ∈ L, b₀⁻¹ * (y * b₀ * y⁻¹) ∈ U ⊓ Subgroup.centralizer (L0 : Set G) := by
    intro y hy
    refine Subgroup.mem_inf.mpr ⟨?_, hwC y hy⟩
    exact U.mul_mem (U.inv_mem hb₀U)
      ((Subgroup.mem_normalizer_iff.mp
        (CFSG.Quasithin.Vol2.Ch10Reselect.L_le_normalizer_fsuUL T L I hy) b₀).mp hb₀U)
  have hb₀Z : b₀ ∈ U ⊓ Subgroup.centralizer (L0 : Set G) := by
    apply hmem b₀ hb₀U
    intro l hl
    have hlV : l * b₀ * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.Quasithin.Vol2.Ch10Reselect.le_normalizer_fsuVM_of_L T L I hl) b₀).mp hb₀V
    have hcm : b₀ * (l * b₀ * l⁻¹) = (l * b₀ * l⁻¹) * b₀ := hcomm b₀ hb₀V _ hlV
    have e : l * b₀ * l⁻¹ * b₀⁻¹ = b₀⁻¹ * (l * b₀ * l⁻¹) := by
      calc l * b₀ * l⁻¹ * b₀⁻¹ = b₀⁻¹ * (b₀ * (l * b₀ * l⁻¹)) * b₀⁻¹ := by group
        _ = b₀⁻¹ * ((l * b₀ * l⁻¹) * b₀) * b₀⁻¹ := by rw [hcm]
        _ = b₀⁻¹ * (l * b₀ * l⁻¹) := by group
    rw [e]
    exact hwZ l hl
  have hb₀C : b₀ ∈ Subgroup.centralizer (L0 : Set G) := (Subgroup.mem_inf.mp hb₀Z).2
  have hbC : b ∈ Subgroup.centralizer (L0 : Set G) := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) b₀).mp hb₀C
    rw [inv_inv] at h
    rw [hb_eq]
    exact h
  have hbC' : b ∈ C := Subgroup.mem_inf.mpr ⟨hbR, hbC⟩
  rw [mul_assoc]
  exact (J ⊔ C).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (C.mul_mem hbC' hc))

end CFSG.Quasithin.Vol2.Ch10Reselect
