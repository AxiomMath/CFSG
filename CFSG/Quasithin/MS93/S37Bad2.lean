module

public import CFSG.Quasithin.MS93.S37Bad

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_eq_of_sup_normal {K H M : Subgroup G} (hKM : K ≤ M) (hHM : H ≤ M)
    (hn : M ≤ Subgroup.normalizer (K : Set G)) (hsup : K ⊔ H = M) :
    K.relIndex M = K.relIndex H := by
  have hKn : (K.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hn
  have h1 := Subgroup.relIndex_sup_right (H.subgroupOf M) (K.subgroupOf M)
  rw [← Subgroup.subgroupOf_sup hHM hKM, sup_comm, hsup, Subgroup.subgroupOf_self,
    Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hHM] at h1
  rw [Subgroup.relIndex, h1]

theorem relIndex_inf_inf_le (A B X : Subgroup G) : (B ⊓ X).relIndex (A ⊓ X) ≤ B.relIndex A := by
  have e : (B ⊓ X).relIndex (A ⊓ X) = B.relIndex (A ⊓ X) := by
    rw [← Subgroup.inf_relIndex_right B (A ⊓ X), ← Subgroup.inf_relIndex_right (B ⊓ X) (A ⊓ X)]
    congr 1
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  rw [e]
  exact Subgroup.relIndex_le_of_le_right inf_le_left (Cfg.relIndex_pos' _ _).ne'

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem rhoIm_Ut_le (θ : MulAut ↥(T1 M T L)) : C.rhoIm (Ut M T L θ) ≤ C.rhoIm (Qt M θ) := by
  intro g hg
  obtain ⟨x, hxK, hx, rfl⟩ := (C.mem_rhoIm).1 hg
  exact (C.mem_rhoIm).2 ⟨x, hxK, tImage_mono' θ C.Uq_le_pCore hx, rfl⟩

theorem rhoIm_Qt_eq_X₂ (θ : MulAut ↥(T1 M T L)) (hE : C.rhoIm (Ut M T L θ) = X₂ F)
    (h : ∀ (z : G) (hz : z ∈ Qt M θ), C.rho ⟨z, Qt_le_sup θ hz⟩ ∈ X₂ F) :
    C.rhoIm (Qt M θ) = X₂ F := by
  refine le_antisymm (fun g hg => ?_) (hE ▸ C.rhoIm_Ut_le θ)
  obtain ⟨z, hzK, hz, rfl⟩ := (C.mem_rhoIm).1 hg
  exact h z hz

theorem rhoIm_Qt_eq_T0bar (θ : MulAut ↥(T1 M T L)) (hE : C.rhoIm (Ut M T L θ) = X₂ F)
    (hK : ∀ (t : G) (ht : t ∈ T ⊓ L), C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩) ∈ X₂ F) :
    C.rhoIm (Qt M θ) = C.T0bar := by
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨z, hzK, hz, rfl⟩ := (C.mem_rhoIm).1 hg
    exact ⟨⟨z, tImage_le θ _ hz⟩, rfl⟩
  · obtain ⟨t, ht, x, hx, rfl⟩ := C.exists_rho_eq_mul θ hg
    refine Subgroup.mul_mem _ ((C.rhoIm_Ut_le θ) (hE ▸ hK t ht)) ?_
    exact (C.mem_rhoIm).2 ⟨_, T1_le_sup (θ ⟨x, C.pCore_le_T1 hx⟩).2,
      mem_tImage.2 ⟨x, C.pCore_le_T1 hx, hx, rfl⟩, rfl⟩

theorem sup_Qt_eq (θ : MulAut ↥(T1 M T L)) (h : C.rhoIm (Qt M θ) = C.T0bar) :
    pCoreOf 2 M ⊔ Qt M θ = T1 M T L := by
  refine le_antisymm (sup_le C.pCore_le_T1 (tImage_le θ _)) fun t ht => ?_
  have hm : C.rho1 ⟨t, ht⟩ ∈ C.rhoIm (Qt M θ) := by
    rw [h]
    exact ⟨_, rfl⟩
  obtain ⟨z, hzK, hz, hρ⟩ := (C.mem_rhoIm).1 hm
  have hyK : z⁻¹ * t ∈ L ⊔ pCoreOf 2 M := (L ⊔ pCoreOf 2 M).mul_mem
    ((L ⊔ pCoreOf 2 M).inv_mem hzK) (T1_le_sup ht)
  have hyQ : z⁻¹ * t ∈ pCoreOf 2 M := by
    refine (C.rho_eq_one_iff ⟨_, hyK⟩).1 ?_
    have e : (⟨z⁻¹ * t, hyK⟩ : ↥(L ⊔ pCoreOf 2 M)) = (⟨z, hzK⟩)⁻¹ * ⟨t, T1_le_sup ht⟩ := rfl
    rw [e, map_mul, map_inv, hρ, C.rho1_apply, inv_mul_cancel]
  have e : t = z * (z⁻¹ * t) := by group
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup hz hyQ

theorem card_UD_eq : Nat.card ↥(Uq M T L ⊔ Dq M L) =
    Nat.card F * Nat.card ↥(C.Usub (perp (pt₀ F)) ⊔ Dq M L) := by
  set P := C.Usub (perp (pt₀ F)) ⊔ Dq M L
  set UD := Uq M T L ⊔ Dq M L
  have hPUD : P ≤ UD := sup_le_sup_right (C.Usub_le _) _
  have hn : UD ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    (sup_le C.Uq_le_pCore inf_le_left).trans ((pCoreOf_le' M).trans C.hMU)
  have hsup : Uq M T L ⊔ P = UD := by
    refine le_antisymm (sup_le le_sup_left hPUD) (sup_le le_sup_left ?_)
    exact le_sup_right.trans le_sup_right
  have e1 := relIndex_eq_of_sup le_sup_left hPUD hn hsup
  rw [← Subgroup.inf_relIndex_right, C.Usub_sup_inf_Uq, C.relIndex_Usub_perp] at e1
  have c := Subgroup.relIndex_mul_card P UD
  rw [inf_eq_left.2 hPUD, ← e1] at c
  exact c.symm

theorem relIndex_Qt_eq_mul (ψ : MulAut ↥(T1 M T L)) (hE : C.rhoIm (Ut M T L ψ) = X₂ F) :
    (pCoreOf 2 M).relIndex (Qt M ψ) =
      (Uq M T L ⊔ Dq M L).relIndex (pCoreOf 2 M) * Nat.card F *
        (Qt M ψ).relIndex (Dq M L) := by
  set H := pCoreOf 2 M ⊓ Qt M ψ with hH
  set P := C.Usub (perp (pt₀ F)) ⊔ Dq M L with hP
  set UD := Uq M T L ⊔ Dq M L with hUD
  have hDQ : Dq M L ≤ pCoreOf 2 M := inf_le_left
  have hUDQ : UD ≤ pCoreOf 2 M := sup_le C.Uq_le_pCore hDQ
  have hHP : H ≤ P := by
    intro x hx
    obtain ⟨u, hu, hd⟩ := C.inf_Qt_of_rhoIm ψ hE x hx
    have e : x = u * (u⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hu hd
  have hsup : Dq M L ⊔ H = P := by
    refine le_antisymm (sup_le le_sup_right hHP) (sup_le ?_ le_sup_left)
    exact (le_inf ((C.Usub_le _).trans C.Uq_le_pCore) (C.Usub_perp_le_Qt ψ hE)).trans
      le_sup_right
  have hPQ : P ≤ pCoreOf 2 M := sup_le ((C.Usub_le _).trans C.Uq_le_pCore) hDQ
  have hn : P ≤ Subgroup.normalizer (Dq M L : Set G) :=
    (hPQ.trans (pCoreOf_le' M)).trans (le_normalizer_Dq C.h.le_normalizer)
  have e1 := relIndex_eq_of_sup (le_sup_right : Dq M L ≤ P) hHP hn hsup
  have e2 : H.relIndex (Dq M L) = (Qt M ψ).relIndex (Dq M L) := by
    rw [← Subgroup.inf_relIndex_right H, ← Subgroup.inf_relIndex_right (Qt M ψ)]
    congr 1
    rw [hH, inf_assoc, inf_eq_right.2 (inf_le_right.trans hDQ : Qt M ψ ⊓ Dq M L ≤ pCoreOf 2 M)]
  have c1 := Subgroup.relIndex_mul_card H P
  rw [inf_eq_left.2 hHP] at c1
  have c2 := Subgroup.relIndex_mul_card (pCoreOf 2 M) (Qt M ψ)
  rw [card_tImage ψ C.pCore_le_T1] at c2
  have c3 := Subgroup.relIndex_mul_card UD (pCoreOf 2 M)
  rw [inf_eq_left.2 hUDQ, C.card_UD_eq] at c3
  have hHpos : 0 < Nat.card ↥H := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hHpos ?_
  rw [c2, ← c3, ← c1, ← e1, e2]
  ring

theorem card_rhoIm_Dt (θ : MulAut ↥(T1 M T L)) :
    Nat.card ↥(C.rhoIm (Dt M L θ)) = (Qt M θ⁻¹).relIndex (Dq M L) := by
  have hDT : Dq M L ≤ T1 M T L := (inf_le_left : Dq M L ≤ pCoreOf 2 M).trans C.pCore_le_T1
  rw [C.card_rhoIm ((tImage_le θ _).trans T1_le_sup),
    ← relIndex_tImage θ⁻¹ C.pCore_le_T1 (tImage_le θ _), tImage_inv_tImage' θ hDT]

theorem conj_mem_Qt_of_T1 (θ : MulAut ↥(T1 M T L)) {t x : G} (ht : t ∈ T1 M T L)
    (hx : x ∈ Qt M θ) : t * x * t⁻¹ ∈ Qt M θ := by
  obtain ⟨y, hyS, hyQ, rfl⟩ := mem_tImage.1 hx
  set s := θ.symm ⟨t, ht⟩
  have hs : (s : G) * y * (s : G)⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf M (C.h.le (T1_le_T s.2))) y).1 hyQ
  refine mem_tImage.2 ⟨_, (T1 M T L).mul_mem ((T1 M T L).mul_mem s.2 hyS)
    ((T1 M T L).inv_mem s.2), hs, ?_⟩
  have e : (⟨(s : G) * y * (s : G)⁻¹, (T1 M T L).mul_mem ((T1 M T L).mul_mem s.2 hyS)
      ((T1 M T L).inv_mem s.2)⟩ : ↥(T1 M T L)) = s * ⟨y, hyS⟩ * s⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rfl

theorem le_normalizer_Dq_sup_Qt (θ : MulAut ↥(T1 M T L)) :
    T1 M T L ≤ Subgroup.normalizer ((Dq M L ⊔ Qt M θ : Subgroup G) : Set G) := by
  have hn : Qt M θ ≤ Subgroup.normalizer (Dq M L : Set G) :=
    (Qt_le_sup θ).trans (C.sup_le_M.trans (le_normalizer_Dq C.h.le_normalizer))
  have hmem : ∀ {t : G}, t ∈ T1 M T L → ∀ h ∈ Dq M L ⊔ Qt M θ, t * h * t⁻¹ ∈ Dq M L ⊔ Qt M θ := by
    intro t ht h hh
    have hh' : h ∈ ((Dq M L ⊔ Qt M θ : Subgroup G) : Set G) := hh
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hh'
    obtain ⟨d, hd, z, hz, rfl⟩ := hh'
    have htM : t ∈ M := C.h.le (T1_le_T ht)
    have e : t * (d * z) * t⁻¹ = (t * d * t⁻¹) * (t * z * t⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem_sup
      ((Subgroup.mem_normalizer_iff.1 (le_normalizer_Dq C.h.le_normalizer htM) d).1 hd)
      (C.conj_mem_Qt_of_T1 θ ht hz)
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hmem ht h, fun hh => ?_⟩
  have := hmem ((T1 M T L).inv_mem ht) _ hh
  simpa [mul_assoc] using this

theorem exists_fix_Dt (θ : MulAut ↥(T1 M T L)) (hE : C.rhoIm (Ut M T L θ) = X₂ F)
    (hK : ∀ (t : G) (ht : t ∈ T ⊓ L), C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩) ∈ X₂ F)
    (hsup : pCoreOf 2 M ⊔ Qt M θ = T1 M T L) :
    ∃ v : V4 F, v ∉ pt₀ F ∧ ∀ (d : G) (hd : d ∈ Dt M L θ),
      mat (C.rho ⟨d, T1_le_sup (tImage_le θ _ hd)⟩) *ᵥ v = v := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  by_contra hcon
  have hfix : ∀ v : V4 F, (∀ (d : G) (hd : d ∈ Dt M L θ),
      mat (C.rho ⟨d, T1_le_sup (tImage_le θ _ hd)⟩) *ᵥ v = v) → v ∈ pt₀ F := by
    intro v hv
    by_contra hv0
    exact hcon ⟨v, hv0, hv⟩
  set H := Dq M L ⊔ Qt M θ with hH
  set T0' := tImage θ (T ⊓ L) with hT0'
  set UD := Uq M T L ⊔ Dq M L with hUD
  set P := C.Usub (perp (pt₀ F)) ⊔ Dq M L with hP
  have hDQ : Dq M L ≤ pCoreOf 2 M := inf_le_left
  have hDT : Dq M L ≤ T1 M T L := hDQ.trans C.pCore_le_T1
  have hHT : H ≤ T1 M T L := sup_le hDT (tImage_le θ _)
  have hHn := C.le_normalizer_Dq_sup_Qt θ
  have hUDQ : UD ≤ pCoreOf 2 M := sup_le C.Uq_le_pCore hDQ
  have hUL : Uq M T L ≤ T ⊓ L := le_inf C.Uq_le_T (Uq_le_L C.h)
  have hUt : Ut M T L θ ≤ T0' := tImage_mono' θ hUL
  have hu1 : T0' ⊓ UD ≤ H := by
    rintro y ⟨hyT, hyUD⟩
    have hn : Uq M T L ≤ Subgroup.normalizer (Dq M L : Set G) :=
      (Uq_le C.h.L_le).trans (le_normalizer_Dq C.h.le_normalizer)
    have hy' : y ∈ ((UD : Subgroup G) : Set G) := hyUD
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hy'
    obtain ⟨u, hu, d, hd, hyud⟩ := hy'
    change u * d = y at hyud
    subst hyud
    obtain ⟨t₀, ht₀T, ht₀, ht₀e⟩ := mem_tImage.1 hyT
    have hfu : ∀ (d' : G) (hd' : d' ∈ Dt M L θ),
        mat (C.rho ⟨d', T1_le_sup (tImage_le θ _ hd')⟩) *ᵥ C.N.co ⟨u, hu⟩ = C.N.co ⟨u, hu⟩ := by
      intro d' hd'
      obtain ⟨d₁, hd₁T, hd₁, rfl⟩ := mem_tImage.1 hd'
      have hc : u * d * ((θ ⟨d₁, hd₁T⟩ : ↥(T1 M T L)) : G) =
          ((θ ⟨d₁, hd₁T⟩ : ↥(T1 M T L)) : G) * (u * d) := by
        have h1 : t₀ * d₁ = d₁ * t₀ := Subgroup.mem_centralizer_iff.1 hd₁.2 t₀ ht₀.2
        have h2 : (⟨t₀, ht₀T⟩ : ↥(T1 M T L)) * ⟨d₁, hd₁T⟩ = ⟨d₁, hd₁T⟩ * ⟨t₀, ht₀T⟩ :=
          Subtype.ext h1
        have h3 := congrArg (fun x => ((θ x : ↥(T1 M T L)) : G)) h2
        simp only [map_mul, Subgroup.coe_mul] at h3
        rw [← ht₀e]
        exact h3
      set e' := ((θ ⟨d₁, hd₁T⟩ : ↥(T1 M T L)) : G)
      have he'M : e' ∈ M := C.h.le (T1_le_T (θ ⟨d₁, hd₁T⟩).2)
      have hcu : e' * u * e'⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (C.hMU he'M) u).1 hu
      have hcd : e' * d * e'⁻¹ ∈ Dq M L :=
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_Dq C.h.le_normalizer he'M) d).1 hd
      have h4 : u⁻¹ * (e' * u * e'⁻¹) = d * (e' * d * e'⁻¹)⁻¹ := by
        have : e' * (u * d) * e'⁻¹ = u * d := by rw [← hc]; group
        calc u⁻¹ * (e' * u * e'⁻¹) = u⁻¹ * (e' * (u * d) * e'⁻¹) * (e' * d * e'⁻¹)⁻¹ := by
              group
          _ = d * (e' * d * e'⁻¹)⁻¹ := by rw [this]; group
      have h5 : C.N.co ⟨u, hu⟩ = C.N.co ⟨e' * u * e'⁻¹, hcu⟩ := by
        rw [C.N.co_eq_co_iff]
        show u⁻¹ * (e' * u * e'⁻¹) ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G)
        refine ⟨(Uq M T L).mul_mem ((Uq M T L).inv_mem hu) hcu, ?_⟩
        rw [h4]
        exact (Subgroup.centralizer _).mul_mem hd.2 ((Subgroup.centralizer _).inv_mem hcd.2)
      exact (C.co_conj ⟨e', T1_le_sup (θ ⟨d₁, hd₁T⟩).2⟩ (u := ⟨u, hu⟩)
        (v := ⟨e' * u * e'⁻¹, hcu⟩) rfl).symm.trans h5.symm
    have hup := hfix _ hfu
    obtain ⟨r, hr, ha⟩ := C.exists_Rt θ hE ((C.mem_Usub).2 ⟨hu, hup⟩)
    have hrQt : r ∈ Qt M θ := by
      have hr' : r ∈ Ut M T L θ := by
        refine (Subgroup.commutator_le.2 fun a ha b hb => ?_) hr
        exact (C.comm_mem_inf C.pCore_le_T1 T1_le_T θ hb ha |>.2 |> fun h => by
          have e : ⁅a, b⁆ = ⁅b, a⁆⁻¹ := by simp only [commutatorElement_def]; group
          rw [e]
          exact (Ut M T L θ).inv_mem h)
      exact tImage_mono' θ C.Uq_le_pCore hr'
    have e : u * d = r * ((r⁻¹ * u) * d) := by group
    rw [e]
    exact H.mul_mem (Subgroup.mem_sup_right hrQt)
      (Subgroup.mem_sup_left ((Dq M L).mul_mem ⟨C.Uq_le_pCore ha.1, ha.2⟩ hd))
  have hu2 : (T0' ⊓ pCoreOf 2 M) ⊔ H = T1 M T L := by
    refine le_antisymm (sup_le (inf_le_right.trans C.pCore_le_T1) hHT) fun t ht => ?_
    obtain ⟨l, hl, q, hq, e⟩ := C.exists_mul_of_mem_T1 (θ⁻¹ ⟨t, ht⟩).2
    have hlT : l ∈ T1 M T L := T_inf_L_le_T1 hl
    have hqT := C.pCore_le_T1 hq
    have hte : t = ((θ ⟨l, hlT⟩ : ↥(T1 M T L)) : G) * ((θ ⟨q, hqT⟩ : ↥(T1 M T L)) : G) := by
      have : (⟨l, hlT⟩ * ⟨q, hqT⟩ : ↥(T1 M T L)) = θ⁻¹ ⟨t, ht⟩ := Subtype.ext e
      have h1 := congrArg (fun x => ((θ x : ↥(T1 M T L)) : G)) this
      simp only [map_mul, Subgroup.coe_mul, MulAut.apply_inv_self] at h1
      exact h1.symm
    have hm : C.rho1 (θ ⟨l, hlT⟩) ∈ C.rhoIm (Ut M T L θ) := by
      rw [hE]
      exact hK l hl
    obtain ⟨u', hu'K, hu', hρ⟩ := (C.mem_rhoIm).1 hm
    set l' := ((θ ⟨l, hlT⟩ : ↥(T1 M T L)) : G)
    have hyK : u'⁻¹ * l' ∈ L ⊔ pCoreOf 2 M := (L ⊔ pCoreOf 2 M).mul_mem
      ((L ⊔ pCoreOf 2 M).inv_mem hu'K) (T1_le_sup (θ ⟨l, hlT⟩).2)
    have hyQ : u'⁻¹ * l' ∈ pCoreOf 2 M := by
      refine (C.rho_eq_one_iff ⟨_, hyK⟩).1 ?_
      have e : (⟨u'⁻¹ * l', hyK⟩ : ↥(L ⊔ pCoreOf 2 M)) =
          (⟨u', hu'K⟩)⁻¹ * ⟨l', T1_le_sup (θ ⟨l, hlT⟩).2⟩ := rfl
      rw [e, map_mul, map_inv, hρ, ← C.rho1_apply, inv_mul_cancel]
    have hyT0 : u'⁻¹ * l' ∈ T0' :=
      T0'.mul_mem (T0'.inv_mem (hUt hu')) (mem_tImage.2 ⟨l, hlT, hl, rfl⟩)
    have hu'Qt : u' ∈ Qt M θ := tImage_mono' θ C.Uq_le_pCore hu'
    have hqQt : ((θ ⟨q, hqT⟩ : ↥(T1 M T L)) : G) ∈ Qt M θ := mem_tImage.2 ⟨q, hqT, hq, rfl⟩
    have hyT1 : u'⁻¹ * l' ∈ T1 M T L := C.pCore_le_T1 hyQ
    have hz : (u'⁻¹ * l')⁻¹ * u' * (u'⁻¹ * l') ∈ Qt M θ := by
      have := C.conj_mem_Qt_of_T1 θ ((T1 M T L).inv_mem hyT1) hu'Qt
      simpa using this
    have e2 : t = (u'⁻¹ * l') * (((u'⁻¹ * l')⁻¹ * u' * (u'⁻¹ * l')) *
        ((θ ⟨q, hqT⟩ : ↥(T1 M T L)) : G)) := by
      rw [hte]
      group
    rw [e2]
    exact Subgroup.mul_mem_sup ⟨hyT0, hyQ⟩ (Subgroup.mem_sup_right ((Qt M θ).mul_mem hz hqQt))
  have hupper : H.relIndex (T1 M T L) ≤ UD.relIndex (pCoreOf 2 M) := by
    rw [relIndex_eq_of_sup_normal hHT (inf_le_right.trans C.pCore_le_T1) hHn
      (by rw [sup_comm]; exact hu2)]
    have h1 : (T0' ⊓ pCoreOf 2 M) ⊓ UD ≤ H := fun x hx => hu1 ⟨hx.1.1, hx.2⟩
    have h2 := Subgroup.relIndex_le_of_le_left (L := T0' ⊓ pCoreOf 2 M)
      (le_inf h1 inf_le_left : (T0' ⊓ pCoreOf 2 M) ⊓ UD ≤ H ⊓ (T0' ⊓ pCoreOf 2 M))
      (Cfg.relIndex_pos' _ _).ne'
    rw [Subgroup.inf_relIndex_right] at h2
    have h3 := relIndex_inf_inf_le (pCoreOf 2 M) UD T0'
    have e3 : (UD ⊓ T0').relIndex (pCoreOf 2 M ⊓ T0') =
        ((T0' ⊓ pCoreOf 2 M) ⊓ UD).relIndex (T0' ⊓ pCoreOf 2 M) := by
      rw [inf_comm (pCoreOf 2 M) T0', ← Subgroup.inf_relIndex_right (UD ⊓ T0'),
        ← Subgroup.inf_relIndex_right ((T0' ⊓ pCoreOf 2 M) ⊓ UD)]
      congr 1
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [e3] at h3
    exact h2.trans h3
  have hlower : UD.relIndex (pCoreOf 2 M) * Nat.card F ≤ H.relIndex (T1 M T L) := by
    rw [relIndex_eq_of_sup_normal hHT C.pCore_le_T1 hHn
      (le_antisymm (sup_le hHT C.pCore_le_T1) (hsup ▸ sup_le le_sup_right
        ((le_sup_right : Qt M θ ≤ H).trans le_sup_left)))]
    have h1 : H ⊓ pCoreOf 2 M ≤ P := by
      rintro x ⟨hxH, hxQ⟩
      have hn : Qt M θ ≤ Subgroup.normalizer (Dq M L : Set G) :=
        (Qt_le_sup θ).trans (C.sup_le_M.trans (le_normalizer_Dq C.h.le_normalizer))
      have hx' : x ∈ ((H : Subgroup G) : Set G) := hxH
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hx'
      obtain ⟨d, hd, z, hz, hxdz⟩ := hx'
      change d * z = x at hxdz
      subst hxdz
      have hzQ : z ∈ pCoreOf 2 M := by
        have e : z = d⁻¹ * (d * z) := by group
        rw [e]
        exact (pCoreOf 2 M).mul_mem ((pCoreOf 2 M).inv_mem (hDQ hd)) hxQ
      obtain ⟨u, hu, hud⟩ := C.inf_Qt_of_rhoIm θ hE z ⟨hzQ, hz⟩
      have e : d * z = (d * u * d⁻¹) * (d * (u⁻¹ * z)) := by group
      have hdu : d * u * d⁻¹ * u⁻¹ ∈ Dq M L := by
        have hdM : d ∈ M := (pCoreOf_le' M) (hDQ hd)
        have hu' := C.Usub_le _ hu
        have e4 : d * u * d⁻¹ * u⁻¹ = d * (u * d⁻¹ * u⁻¹) := by group
        rw [e4]
        exact (Dq M L).mul_mem hd ((Subgroup.mem_normalizer_iff.1
          (le_normalizer_Dq C.h.le_normalizer ((Uq_le C.h.L_le) hu')) _).1 ((Dq M L).inv_mem hd))
      have e5 : d * z = u * ((u⁻¹ * (d * u * d⁻¹ * u⁻¹) * u) * (d * (u⁻¹ * z))) := by group
      rw [e5]
      refine Subgroup.mul_mem_sup hu ((Dq M L).mul_mem ?_ ((Dq M L).mul_mem hd hud))
      have hu' := C.Usub_le _ hu
      have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_Dq C.h.le_normalizer
        ((Uq_le C.h.L_le) ((Uq M T L).inv_mem hu'))) _).1 hdu
      simpa using this
    have h2 := Subgroup.relIndex_le_of_le_left (L := pCoreOf 2 M) h1 (Cfg.relIndex_pos' _ _).ne'
    rw [Subgroup.inf_relIndex_right] at h2
    have hPUD : P ≤ UD := sup_le_sup_right (C.Usub_le _) _
    have h3 := Subgroup.relIndex_mul_relIndex P UD (pCoreOf 2 M) hPUD hUDQ
    have h4 : P.relIndex UD = Nat.card F := by
      have c := Subgroup.relIndex_mul_card P UD
      rw [inf_eq_left.2 hPUD, C.card_UD_eq] at c
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos c
    rw [h4] at h3
    rw [mul_comm, h3]
    exact h2
  have hr : 0 < UD.relIndex (pCoreOf 2 M) := Cfg.relIndex_pos' _ _
  have hq := C.q_ge_four
  have : UD.relIndex (pCoreOf 2 M) * Nat.card F ≤ UD.relIndex (pCoreOf 2 M) * 1 :=
    (hlower.trans hupper).trans (by rw [mul_one])
  have := Nat.le_of_mul_le_mul_left this hr
  omega

end Cfg

end CFSG.Quasithin.MS93.S37
