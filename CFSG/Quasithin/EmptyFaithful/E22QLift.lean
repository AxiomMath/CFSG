module

public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.E1Sec7Two

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b

variable {G : Type} [Group G] [Finite G]

@[expose] def WitnessL2 (p : ℕ) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (J T A : Subgroup H) [J.Normal], IsPSL 2 p 1 ↥J →
    Subgroup.centralizer (J : Set H) = ⊥ → IsSylowIn 2 T ⊤ → J ⊔ T = ⊤ →
    ∀ z : H, orderOf z = 2 → (∀ x ∈ T, z * x = x * z) →
    A ≤ T → IsElemAbelian 2 A → A ≠ ⊥ →
    ∃ K : Subgroup H, E1.IsE 1 ⊤ T A K ∧ ¬ K ≤ Subgroup.centralizer ({z} : Set H)

theorem isSylowIn_top_map {H H' : Type} [Group H] [Group H'] [Finite H] (f : H →* H')
    (hf : Function.Surjective f) {T : Subgroup H} (hT : IsSylowIn 2 T ⊤) :
    IsSylowIn 2 (T.map f) ⊤ := by
  refine ⟨le_top, hT.isPGroup.map f, ?_⟩
  have h1 := hT.not_dvd_relIndex
  rw [Subgroup.relIndex_top_right] at h1 ⊢
  intro hd
  apply h1
  exact hd.trans (Subgroup.index_map_dvd T hf)

theorem isElemAbelian_map_hom {H H' : Type} [Group H] [Group H'] (f : H →* H') {p : ℕ}
    {A : Subgroup H} (h : IsElemAbelian p A) : IsElemAbelian p (A.map f) :=
  CFSG.Open.IsElemAbelian.map h _

theorem isElemAbelian_of_map_injective' {H H' : Type} [Group H] [Group H'] {f : H →* H'}
    (hf : Function.Injective f) {p : ℕ} {A : Subgroup H} (h : IsElemAbelian p (A.map f)) :
    IsElemAbelian p A := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have := h.1.is_comm.comm ⟨f x, x, x.2, rfl⟩ ⟨f y, y, y.2, rfl⟩
    exact hf (by simpa [map_mul] using congrArg Subtype.val this)
  · exact hf (by simpa [map_pow] using h.2 (f x) ⟨x, hx, rfl⟩)

omit [Finite G] in
theorem isElemAbelian_subgroupOf {Q A : Subgroup G} (_hAQ : A ≤ Q) {p : ℕ}
    (h : IsElemAbelian p A) : IsElemAbelian p (A.subgroupOf Q) :=
  CFSG.Open.IsElemAbelian.subgroupOf h Q

theorem local_witness {p : ℕ} (hW : WitnessL2 p) {T A Q D : Subgroup G} {z : G}
    (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hDQ : D ≤ Q) (hDn : (D.subgroupOf Q).Normal) (hDp : IsPSL 2 p 1 ↥D)
    (hDs : IsSimpleGroup ↥D) (hDnc : ∃ a b : ↥D, a * b ≠ b * a)
    (hTQ : IsSylowIn 2 (T ⊓ Q) Q) (hQ : D ⊔ (T ⊓ Q) = Q)
    (hτ : E1.tauOf ⊤ T A ≤ T ⊓ Q) (hAQ : A ≤ Q)
    (hAD : ¬ A ≤ Subgroup.centralizer (D : Set G))
    (hzD : z ∈ D) (hz2 : orderOf z = 2) (hzc : ∀ x ∈ T ⊓ Q, z * x = x * z) :
    ∃ J : Subgroup G, J ≤ Q ∧ E1.IsE 1 ⊤ T A J ∧ ¬ J ≤ Subgroup.centralizer ({z} : Set G) := by
  have hTQle : T ⊓ Q ≤ Q := inf_le_right
  have hDle : D ≤ Q := hDQ
  set Y : Subgroup ↥Q := (Subgroup.centralizer (D : Set G)).subgroupOf Q with hY
  have hYn : Y.Normal := by
    refine ⟨fun y hy q => ?_⟩
    rw [hY, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hy ⊢
    intro d hd
    have hd' : (q : G)⁻¹ * d * (q : G) ∈ D := by
      have := hDn.conj_mem ⟨d, hDle hd⟩ (Subgroup.mem_subgroupOf.mpr hd) q⁻¹
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have h1 := hy _ hd'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1 ⊢
    calc d * ((q : G) * (y : G) * (q : G)⁻¹) = (q : G) * ((q : G)⁻¹ * d * (q : G) * (y : G)) *
          (q : G)⁻¹ := by group
      _ = (q : G) * ((y : G) * ((q : G)⁻¹ * d * (q : G))) * (q : G)⁻¹ := by rw [h1]
      _ = (q : G) * (y : G) * (q : G)⁻¹ * d := by group
  have : Y.Normal := hYn
  set π : ↥Q →* ↥Q ⧸ Y := QuotientGroup.mk' Y with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  have hZ : Subgroup.center ↥D = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hDnc).2
  have hDC : ∀ d ∈ D, d ∈ Subgroup.centralizer (D : Set G) → d = 1 := by
    intro d hd hdC
    have hmem : (⟨d, hd⟩ : ↥D) ∈ Subgroup.center ↥D := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hdC y y.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  set DQ : Subgroup ↥Q := D.subgroupOf Q with hDQdef
  set TQ : Subgroup ↥Q := (T ⊓ Q).subgroupOf Q with hTQdef
  set AQ : Subgroup ↥Q := A.subgroupOf Q with hAQdef
  have hATQ : A ≤ T ⊓ Q := le_inf hAT hAQ
  have hinj : ∀ a b : ↥Q, a ∈ DQ → b ∈ DQ → π a = π b → a = b := by
    intro a b ha hb hab
    have h1 : a⁻¹ * b ∈ Y := QuotientGroup.eq.mp hab
    rw [hY, Subgroup.mem_subgroupOf] at h1
    have h2 : (a⁻¹ * b : ↥Q) ∈ DQ := DQ.mul_mem (DQ.inv_mem ha) hb
    rw [hDQdef, Subgroup.mem_subgroupOf] at h2
    have h3 := hDC _ h2 h1
    have : a⁻¹ * b = 1 := Subtype.ext h3
    exact inv_mul_eq_one.mp this
  set JH : Subgroup (↥Q ⧸ Y) := DQ.map π with hJH
  have hJHn : JH.Normal := Subgroup.Normal.map hDn π hπs
  have hJHp : IsPSL 2 p 1 ↥JH := by
    let φ : ↥DQ →* ↥JH := π.subgroupMap DQ
    have hφi : Function.Injective φ := by
      intro a b hab
      have : π (a : ↥Q) = π (b : ↥Q) := congrArg Subtype.val hab
      exact Subtype.ext (hinj _ _ a.2 b.2 this)
    have hφs : Function.Surjective φ := π.subgroupMap_surjective DQ
    let e : ↥D ≃* ↥JH := (Subgroup.subgroupOfEquivOfLe hDle).symm.trans
      (MulEquiv.ofBijective φ ⟨hφi, hφs⟩)
    exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e.symm hDp
  have hCJH : Subgroup.centralizer (JH : Set (↥Q ⧸ Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    obtain ⟨q, rfl⟩ := hπs h
    rw [Subgroup.mem_bot]
    have hqY : q ∈ Y := by
      rw [hY, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro d hd
      have hdQ : (⟨d, hDle hd⟩ : ↥Q) ∈ DQ := Subgroup.mem_subgroupOf.mpr hd
      have hc := Subgroup.mem_centralizer_iff.mp hh (π ⟨d, hDle hd⟩) (Subgroup.mem_map_of_mem π hdQ)
      have h1 : (q⁻¹ * ⟨d, hDle hd⟩⁻¹ * q * ⟨d, hDle hd⟩ : ↥Q) ∈ Y := by
        have hc' : π (⟨d, hDle hd⟩ * q) = π (q * ⟨d, hDle hd⟩) := by
          rw [map_mul, map_mul]; exact hc
        have := QuotientGroup.eq.mp hc'
        simpa [mul_assoc] using this
      have h2 : (q⁻¹ * ⟨d, hDle hd⟩⁻¹ * q * ⟨d, hDle hd⟩ : ↥Q) ∈ DQ := by
        refine DQ.mul_mem (?_) hdQ
        have := hDn.conj_mem _ (DQ.inv_mem hdQ) q⁻¹
        simpa [mul_assoc] using this
      rw [hY, Subgroup.mem_subgroupOf] at h1
      rw [hDQdef, Subgroup.mem_subgroupOf] at h2
      have h3 := hDC _ h2 h1
      have h4 : (q⁻¹ * ⟨d, hDle hd⟩⁻¹ * q * ⟨d, hDle hd⟩ : ↥Q) = 1 := Subtype.ext h3
      have h5 : (⟨d, hDle hd⟩ : ↥Q) * q = q * ⟨d, hDle hd⟩ := by
        have h6 : q⁻¹ * (⟨d, hDle hd⟩⁻¹ * q * ⟨d, hDle hd⟩ : ↥Q) = 1 := by
          rw [← h4]; group
        have h7 : q = (⟨d, hDle hd⟩⁻¹ * q * ⟨d, hDle hd⟩ : ↥Q) := inv_mul_eq_one.mp h6
        calc (⟨d, hDle hd⟩ : ↥Q) * q = ⟨d, hDle hd⟩ * (⟨d, hDle hd⟩⁻¹ * q * ⟨d, hDle hd⟩) := by
              rw [← h7]
          _ = q * ⟨d, hDle hd⟩ := by group
      exact congrArg Subtype.val h5
    exact (QuotientGroup.eq_one_iff q).mpr hqY
  have hTQ' : IsSylowIn 2 TQ ⊤ := by
    have h := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := T ⊓ Q) (K := Q) (H := Q) hTQle
      le_rfl).mpr hTQ
    rwa [Subgroup.subgroupOf_self] at h
  set TH : Subgroup (↥Q ⧸ Y) := TQ.map π with hTH
  have hTH' : IsSylowIn 2 TH ⊤ := isSylowIn_top_map π hπs hTQ'
  have hJT : JH ⊔ TH = ⊤ := by
    have h1 : DQ ⊔ TQ = ⊤ := by
      rw [hDQdef, hTQdef, ← Subgroup.subgroupOf_sup hDle hTQle, hQ, Subgroup.subgroupOf_self]
    rw [hJH, hTH, ← Subgroup.map_sup, h1, Subgroup.map_top_of_surjective π hπs]
  have hzQ : z ∈ Q := hDle hzD
  set zQ : ↥Q := ⟨z, hzQ⟩ with hzQdef
  have hzY : zQ ∉ Y := by
    intro h
    rw [hY, Subgroup.mem_subgroupOf] at h
    have := hDC z hzD h
    rw [this, orderOf_one] at hz2
    omega
  have hz2' : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2] at this
  have hzQ2 : zQ ^ 2 = 1 := Subtype.ext (by simpa using hz2')
  have hzH2 : orderOf (π zQ) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hzQ2, map_one]
    · intro h
      exact hzY ((QuotientGroup.eq_one_iff zQ).mp h)
  have hzHc : ∀ x ∈ TH, π zQ * x = x * π zQ := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have ht' : (t : G) ∈ T ⊓ Q := Subgroup.mem_subgroupOf.mp ht
    exact Subtype.ext (hzc _ ht')
  have hAQ' : AQ ≤ TQ := by
    intro a ha
    exact Subgroup.mem_subgroupOf.mpr (hATQ (Subgroup.mem_subgroupOf.mp ha))
  set AH : Subgroup (↥Q ⧸ Y) := AQ.map π with hAH
  have hAHT : AH ≤ TH := Subgroup.map_mono hAQ'
  have hAHab : IsElemAbelian 2 AH := isElemAbelian_map_hom π (isElemAbelian_subgroupOf hAQ hAab)
  have hAH1 : AH ≠ ⊥ := by
    intro hbot
    apply hAD
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have haQ : (⟨a, hAQ ha⟩ : ↥Q) ∈ AQ := Subgroup.mem_subgroupOf.mpr ha
    have h1 : π ⟨a, hAQ ha⟩ ∈ AH := Subgroup.mem_map_of_mem π haQ
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨a, hAQ ha⟩ : ↥Q) ∈ Y := (QuotientGroup.eq_one_iff _).mp h1
    rw [hY, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h2
    exact h2 d hd
  obtain ⟨I, hI, hIz⟩ := hW (↥Q ⧸ Y) JH TH AH hJHp hCJH hTH' hJT (π zQ) hzH2 hzHc hAHT hAHab hAH1
  have hAQT : AQ ≤ TQ := hAQ'
  obtain ⟨J', hJ', hJ'r⟩ := E1.ten_seven (G := ↥Q) (Y := Y) hTQ' hAQT
    (isElemAbelian_subgroupOf hAQ hAab) (i := 1) (I := I) hI
  set J : Subgroup G := J'.map Q.subtype with hJ
  have hJle : J ≤ Q := Subgroup.map_subtype_le J'
  have hTQmap : TQ.map Q.subtype = T ⊓ Q := Subgroup.map_subgroupOf_eq_of_le hTQle
  have hAQmap : AQ.map Q.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAQ
  have hJE : E1.IsE 1 Q (T ⊓ Q) A J := by
    have := (E1.isE_map_subtype (i := 1) Q (T' := TQ) (A' := AQ) (K' := J')).mpr hJ'
    rwa [hTQmap, hAQmap] at this
  have hJE' : E1.IsE 1 ⊤ T A J := E1.eight_two hT hAT hAab le_top hτ hTQ hJE
  refine ⟨J, hJle, hJE', ?_⟩
  intro hJz
  apply hIz
  have hJ'z : ∀ x ∈ J', zQ * x = x * zQ := by
    intro x hx
    have hxJ : (x : G) ∈ J := ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hJz hxJ) z rfl
    exact Subtype.ext this
  have hcomm : J'.map π ≤ Subgroup.centralizer ({π zQ} : Set (↥Q ⧸ Y)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul, hJ'z x hx]
  have h1 : twoResidual I ≤ Subgroup.centralizer ({π zQ} : Set (↥Q ⧸ Y)) := by
    rw [hJ'r]
    exact (Subgroup.map_mono (twoResidual_le J')).trans hcomm
  have h2 : I ≤ twoResidual I ⊔ (TH ⊓ I) := E1.le_twoResidual_sup_of_isSylowIn hI.2.2.1
  have hTHle : TH ≤ Subgroup.centralizer ({π zQ} : Set (↥Q ⧸ Y)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hzHc x hx
  exact h2.trans (sup_le h1 (inf_le_left.trans hTHle))

end CFSG.Quasithin.E2.E22N
