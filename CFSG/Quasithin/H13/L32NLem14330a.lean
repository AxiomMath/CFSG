module

public import CFSG.Quasithin.H13.L32NLem14328d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14328

variable {G : Type} [Group G]

omit [Group G] in
theorem conjugate_inv_mem_iff [Group G] {X : Subgroup G} {m x : G} :
    x ∈ CFSG.conjugate X m⁻¹ ↔ m⁻¹ * x * m ∈ X := by
  rw [mem_conj_iff, inv_inv]

theorem conjugate_le_normalizer {T L : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) (hT : T ≤ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate T m⁻¹ ≤ Subgroup.normalizer (L : Set G) := by
  intro x hx
  rw [conjugate_inv_mem_iff] at hx
  have h1 := hT hx
  have h2 : m * (m⁻¹ * x * m) * m⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hm h1)
      ((Subgroup.normalizer _).inv_mem hm)
  rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at h2

theorem sup_conjugate_eq {T L : Subgroup G} {m : G} (hm : m ∈ L) :
    L ⊔ CFSG.conjugate T m⁻¹ = L ⊔ T := by
  apply le_antisymm
  · refine sup_le le_sup_left fun x hx => ?_
    rw [conjugate_inv_mem_iff] at hx
    have : m * (m⁻¹ * x * m) * m⁻¹ ∈ L ⊔ T :=
      (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right hx))
        ((L ⊔ T).inv_mem (Subgroup.mem_sup_left hm))
    rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at this
  · refine sup_le le_sup_left fun x hx => ?_
    have hx' : m * x * m⁻¹ ∈ CFSG.conjugate T m⁻¹ := by
      rw [conjugate_inv_mem_iff]
      simpa [mul_assoc] using hx
    have : m⁻¹ * (m * x * m⁻¹) * m ∈ L ⊔ CFSG.conjugate T m⁻¹ :=
      (L ⊔ _).mul_mem ((L ⊔ _).mul_mem (Subgroup.mem_sup_left (L.inv_mem hm))
        (Subgroup.mem_sup_right hx')) (Subgroup.mem_sup_left hm)
    rwa [show m⁻¹ * (m * x * m⁻¹) * m = x by group] at this

theorem index_subgroupOf_conjugate {T K : Subgroup G} {m : G} (hm : m ∈ K) :
    ((CFSG.conjugate T m⁻¹).subgroupOf K).index = (T.subgroupOf K).index := by
  have h1 : (CFSG.conjugate T m⁻¹).relIndex (CFSG.conjugate K m⁻¹) = T.relIndex K :=
    Subgroup.relIndex_map_map_of_injective T K (MulAut.conj m⁻¹⁻¹).injective
  have hK : CFSG.conjugate K m⁻¹ = K := L14328.conjugate_eq_self
    (Subgroup.le_normalizer (K.inv_mem hm))
  rw [hK] at h1
  exact h1

theorem isLocal_conjugate {T K : Subgroup G} {m : G} (hm : m ∈ K)
    (h : quasithinIsLocal T K) : quasithinIsLocal (CFSG.conjugate T m⁻¹) K := by
  obtain ⟨hT2, hc, hidx, hO⟩ := h
  have hsup := sup_conjugate_eq (T := T) hm
  refine ⟨hT2.map _, hsup ▸ hc, ?_, hsup ▸ hO⟩
  rw [hsup]
  rw [index_subgroupOf_conjugate (Subgroup.mem_sup_left hm)]
  exact hidx

theorem isLocal_of_conjugate {T K : Subgroup G} {m : G} (hm : m ∈ K)
    (h : quasithinIsLocal (CFSG.conjugate T m⁻¹) K) : quasithinIsLocal T K := by
  have h' := isLocal_conjugate (T := CFSG.conjugate T m⁻¹) (K.inv_mem hm) h
  have e : CFSG.conjugate (CFSG.conjugate T m⁻¹) m⁻¹⁻¹ = T := by
    ext x
    rw [mem_conj_iff, mem_conj_iff]
    simp only [inv_inv]
    rw [show m⁻¹ * (m * x * m⁻¹) * m = x by group]
  rwa [e] at h'

theorem isSylowTwo_conjugate {T : Subgroup G} (h : quasithinIsSylowTwo T) (m : G) :
    quasithinIsSylowTwo (CFSG.conjugate T m⁻¹) := by
  refine ⟨h.1.map _, ?_⟩
  have := Subgroup.index_map_equiv T (MulAut.conj m⁻¹⁻¹)
  rw [CFSG.conjugate]
  rw [show (MulAut.conj m⁻¹⁻¹ : G →* G) = (MulAut.conj m⁻¹⁻¹).toMonoidHom from rfl] at this
  rw [this]
  exact h.2

theorem conjClosure_eq_of_le {X H : Subgroup G} (h : H ≤ Subgroup.normalizer (X : Set G)) :
    conjClosure X H = X :=
  le_antisymm (conjClosure_le fun _ hh _ hx => (Subgroup.mem_normalizer_iff.mp (h hh) _).mp hx)
    (le_conjClosure X H)

theorem isIrrPlusIn_congr {X A Y Y' I : Subgroup G} (h : conjClosure I Y = conjClosure I Y')
    (hI : IsIrrPlusIn X A Y I) : IsIrrPlusIn X A Y' I := by
  unfold IsIrrPlusIn at hI ⊢
  rwa [← h]

variable [Finite G]

theorem hyp1223_conj {T L V : Subgroup G} (h : Hyp1223 G T L V)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) {m : G} (hm : m ∈ L) :
    Hyp1223 G (CFSG.conjugate T m⁻¹) L V where
  simple := h.simple
  nonabelian := h.nonabelian
  qtke := h.qtke
  sylow := isSylowTwo_conjugate h.sylow m
  notAlt := h.notAlt
  maximal := ⟨isLocal_conjugate hm h.maximal.1, fun K hK hLK =>
    h.maximal.2 K (isLocal_of_conjugate (hLK hm) hK) hLK⟩
  faithful := ⟨isLocal_conjugate hm h.faithful.1, h.faithful.2⟩
  quasisimple := h.quasisimple
  normalizes := conjugate_le_normalizer (Subgroup.le_normalizer hm) h.normalizes
  irrPlus := by
    have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.irrPlus.2.2.1
    have hTV' : CFSG.conjugate T m⁻¹ ≤ Subgroup.normalizer (V : Set G) :=
      conjugate_le_normalizer (hLV hm) hTV
    have := isIrrPlusIn_congr (Y' := CFSG.conjugate T m⁻¹)
      ((conjClosure_eq_of_le hTV).trans (conjClosure_eq_of_le hTV').symm) h.irrPlus
    rw [sup_conjugate_eq hm]
    exact this

theorem hyp1281One_conj {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) {m : G} (hm : m ∈ L) :
    Hyp1281One G (CFSG.conjugate T m⁻¹) L V n where
  hyp := hyp1223_conj h.hyp hTV hm
  n_mem := h.n_mem
  quot := h.quot
  natural := h.natural
  not_linear := h.not_linear
  not_alt9 := h.not_alt9
  not_m24 := h.not_m24

omit [Finite G] in
theorem isTSub_conj {T V W : Subgroup G} {i : ℕ} (h : IsTSub T V W i) {m : G}
    (hmV : m ∈ Subgroup.normalizer (V : Set G)) :
    IsTSub (CFSG.conjugate T m⁻¹) V (CFSG.conjugate W m⁻¹) i := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [conjugate_inv_mem_iff] at hx
    have := (Subgroup.mem_normalizer_iff.mp hmV _).mp (h.1 hx)
    rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at this
  · rw [← h.2.1, CFSG.conjugate]
    exact Subgroup.card_map_of_injective (MulAut.conj m⁻¹⁻¹).injective
  · intro x hx
    rw [conjugate_inv_mem_iff] at hx
    have hx' := h.2.2 hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [conjugate_inv_mem_iff, conjugate_inv_mem_iff]
    have := Subgroup.mem_normalizer_iff.mp hx' (m⁻¹ * y * m)
    rwa [show m⁻¹ * x * m * (m⁻¹ * y * m) * (m⁻¹ * x * m)⁻¹ = m⁻¹ * (x * y * x⁻¹) * m by group]
      at this

theorem setting1282One_conj {T L V V₁ V₂ : Subgroup G} {n : ℕ}
    (hs : Setting1282One G T L V n V₁ V₂) (hTV : T ≤ Subgroup.normalizer (V : Set G)) {m : G}
    (hm : m ∈ L) :
    Setting1282One G (CFSG.conjugate T m⁻¹) L V n (CFSG.conjugate V₁ m⁻¹)
      (CFSG.conjugate V₂ m⁻¹) where
  hyp := hyp1281One_conj hs.hyp hTV hm
  v1 := isTSub_conj hs.v1 (hs.hyp.hyp.irrPlus.2.2.1 hm)
  v2 := isTSub_conj hs.v2 (hs.hyp.hyp.irrPlus.2.2.1 hm)
  le := conjugate_mono hs.le _
  nonabelian := by
    have hmV : m⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      (Subgroup.normalizer _).inv_mem (hs.hyp.hyp.irrPlus.2.2.1 hm)
    have e : u128 V (CFSG.conjugate V₁ m⁻¹) = CFSG.conjugate (u128 V V₁) m⁻¹ := by
      rw [u128, u128, conjugate_conjClosure, conjugate_normalizer, conjugate_eq_self hmV]
    rw [e]
    intro hc
    apply hs.nonabelian
    refine ⟨⟨fun x y => ?_⟩⟩
    have hx : m * (x : G) * m⁻¹ ∈ CFSG.conjugate (u128 V V₁) m⁻¹ := by
      rw [conjugate_inv_mem_iff]; simp [mul_assoc]
    have hy : m * (y : G) * m⁻¹ ∈ CFSG.conjugate (u128 V V₁) m⁻¹ := by
      rw [conjugate_inv_mem_iff]; simp [mul_assoc]
    have := congrArg Subtype.val (hc.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
    simp only [Subgroup.coe_mul] at this
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (x : G) * y = m⁻¹ * ((m * x * m⁻¹) * (m * y * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * y * m⁻¹) * (m * x * m⁻¹)) * m := by rw [this]
      _ = y * x := by group

end L14328

end CFSG.Quasithin.H13
