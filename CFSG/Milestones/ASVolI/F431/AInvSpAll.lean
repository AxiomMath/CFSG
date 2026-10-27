module

import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F431.JRed2

public section

namespace CFSG.ASVolI

section MixedCent

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.ASVolI.ChF

variable {K : Type} [Field K]

theorem burnsideF4m_centralizer_mixed_le :
    Subgroup.centralizer ({burnsideF4gSpInv_xl (1 : K) * burnsideF4gSpInv_xs 1} :
      Set (StatedSp 2 K)) ≤ Q2 K 1 := by
  set m : StatedSp 2 K := burnsideF4gSpInv_xl (1 : K) * burnsideF4gSpInv_xs 1 with hm
  have key : ∀ g : StatedSp 2 K, g * m = m * g →
      ∀ w ∈ flag 2 K 2, burnsideF4gSpInv_mv g w ∈ flag 2 K 2 := by
    intro g hg w hw
    rw [burnsideF4gSpInv_mem_flag_two] at hw
    obtain ⟨u, hu⟩ : ∃ u : Fin 2 ⊕ Fin 2 → K, u = (w (Sum.inl 1)) • Pi.single (Sum.inr 0) 1 +
        (w (Sum.inl 0) - w (Sum.inl 1)) • Pi.single (Sum.inr 1) 1 := ⟨_, rfl⟩
    have hxu : burnsideF4gSpInv_mv m u - u = w := by
      rw [hm, burnsideF4gSpInv_mixed_mv, hu]
      ext i
      rcases i with i | i <;> fin_cases i <;> simp [Pi.single_apply, hw.1, hw.2]
    have h1 : burnsideF4gSpInv_mv g w = burnsideF4gSpInv_mv m
        (burnsideF4gSpInv_mv g u) - burnsideF4gSpInv_mv g u := by
      calc burnsideF4gSpInv_mv g w
          = burnsideF4gSpInv_mv g (burnsideF4gSpInv_mv m u - u) := by rw [hxu]
        _ = burnsideF4gSpInv_mv g (burnsideF4gSpInv_mv m u) -
              burnsideF4gSpInv_mv g u := burnsideF4gSpInv_mv_sub _ _ _
        _ = _ := by rw [← burnsideF4gSpInv_mv_mul, hg, burnsideF4gSpInv_mv_mul]
    rw [h1, hm, burnsideF4gSpInv_mixed_mv, add_assoc, add_sub_cancel_left,
      burnsideF4gSpInv_mem_flag_two]
    simp [Pi.single_apply]
  intro g hg
  have hg' := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hginv := Subgroup.mem_centralizer_singleton_iff.1
    ((Subgroup.centralizer ({m} : Set (StatedSp 2 K))).inv_mem hg)
  rw [burnsideF4gSpInv_mem_Q2_one]
  intro v
  constructor
  · intro h
    have := key g⁻¹ hginv _ h
    rwa [burnsideF4gSpInv_mv_mv_inv] at this
  · exact key g hg' v

end MixedCent

section Burnside

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChF

variable {G : Type} [Group G] [Finite G]

theorem burnsideF4m_burnside {H S : Subgroup G} (hS : ChF.IsSylowOf 2 S H) {w : G}
    (hw : w ∈ ctr S) {n : G} (hn : n ∈ H) (hnw : n * w * n⁻¹ ∈ ctr S) :
    ∃ b ∈ H ⊓ Subgroup.normalizer (S : Set G), b * w * b⁻¹ = n * w * n⁻¹ := by
  set y := n * w * n⁻¹ with hy
  set C : Subgroup G := H ⊓ Subgroup.centralizer ({y} : Set G) with hC
  have hSC : S ≤ C := fun s hs => ⟨hS.1 hs, Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 hnw.2 s hs)⟩
  have hnSC : conjSub n S ≤ C := by
    intro z hz
    have hs : n⁻¹ * z * n ∈ S := mem_conjSub.mp hz
    have hz' : z = n * (n⁻¹ * z * n) * n⁻¹ := by group
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · rw [hz']
      exact H.mul_mem (H.mul_mem hn (hS.1 hs)) (H.inv_mem hn)
    · have hcw : (n⁻¹ * z * n) * w = w * (n⁻¹ * z * n) :=
        Subgroup.mem_centralizer_iff.1 hw.2 _ hs
      rw [hz', hy]
      calc n * (n⁻¹ * z * n) * n⁻¹ * (n * w * n⁻¹) = n * ((n⁻¹ * z * n) * w) * n⁻¹ := by group
        _ = n * (w * (n⁻¹ * z * n)) * n⁻¹ := by rw [hcw]
        _ = n * w * n⁻¹ * (n * (n⁻¹ * z * n) * n⁻¹) := by group
  have hS1 : ChF.IsSylowOf 2 S C := F7.isSylowTwoOf_mono_right hS hSC inf_le_left
  have hnS : ChF.IsSylowOf 2 (conjSub n S) H := burnsideF4ja_isSylowOf_conjSub hS hn
  have hnS1 : ChF.IsSylowOf 2 (conjSub n S) C :=
    F7.isSylowTwoOf_mono_right hnS hnSC inf_le_left
  obtain ⟨m, hm, hmeq⟩ := burnsideF4ja_sylow_conj hS1 hnS1
  have hkey : ∀ x, x ∈ conjSub (m * n) S ↔ x ∈ conjSub m (conjSub n S) := by
    intro x
    rw [mem_conjSub, mem_conjSub, mem_conjSub]
    have e : (m * n)⁻¹ * x * (m * n) = n⁻¹ * (m⁻¹ * x * m) * n := by group
    rw [e]
  have hb : conjSub (m * n) S = S := by
    ext x
    rw [hkey x, ← hmeq]
  refine ⟨m * n, ⟨H.mul_mem hm.1 hn, burnsideF4ja_mem_normalizer_of_conjSub_eq hb⟩, ?_⟩
  have hmy : m * y = y * m := Subgroup.mem_centralizer_singleton_iff.1 hm.2
  calc m * n * w * (m * n)⁻¹ = m * y * m⁻¹ := by rw [hy]; group
    _ = y := by rw [hmy]; group

end Burnside

section CentLe

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChF

variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_centralizer_le_of_ctr (hyp : HypF_4_4g κ 2 f Gp M₁ M₂)
    (hSyl : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp)
    (hN : Gp ⊓ Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) ≤
      M₁ ⊓ M₂) {w : E}
    (hw : w ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) {M : Subgroup E} (hM : M₁ ⊓ M₂ ≤ M)
    (hC : ∀ n ∈ Gp, n * w = w * n → n ∈ M) :
    Subgroup.centralizer ({w} : Set E) ≤ M := by
  haveI := hyp.finite
  intro c hc
  obtain ⟨n, hn, h, hh, rfl⟩ := hyp.split c
  have hhN : h ∈ Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (burnsideF4j_le_normalizer_inf hyp.normal (M₁ ⊓ M₂) hh)
  have hhZ : h ∈ Subgroup.normalizer ((ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) : Subgroup E) :
      Set E) := burnsideF4j_mem_normalizer_ctr hhN
  have hhw : h * w * h⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) :=
    (Subgroup.mem_normalizer_iff.mp hhZ w).mp hw
  have hcw : n * h * w = w * (n * h) := Subgroup.mem_centralizer_singleton_iff.mp hc
  have he : n⁻¹ * w * n⁻¹⁻¹ = h * w * h⁻¹ := by
    calc n⁻¹ * w * n⁻¹⁻¹ = n⁻¹ * (w * (n * h)) * h⁻¹ := by group
      _ = n⁻¹ * (n * h * w) * h⁻¹ := by rw [hcw]
      _ = h * w * h⁻¹ := by group
  obtain ⟨b, hb, hbw⟩ := burnsideF4m_burnside hSyl hw (Gp.inv_mem hn) (he ▸ hhw)
  have hbM : b ∈ M := hM (hN hb)
  have hnb : n * b * w = w * (n * b) := by
    have h1 : b * w * b⁻¹ = n⁻¹ * w * n := by rw [hbw, inv_inv]
    calc n * b * w = n * (b * w * b⁻¹) * b := by group
      _ = n * (n⁻¹ * w * n) * b := by rw [h1]
      _ = w * (n * b) := by group
  have hnbM : n * b ∈ M := hC (n * b) (Gp.mul_mem hn hb.1) hnb
  have hnM : n ∈ M := by
    have := M.mul_mem hnbM (M.inv_mem hbM)
    simpa using this
  exact M.mul_mem hnM (hM hh)

end CentLe

section Sp4Gp

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF4m_isSylowTwoOf_map_inj {D H : Type} [Group D] [Group H] (Φ : D →* H)
    (hΦ : Function.Injective Φ) {S X : Subgroup D} (h : IsSylowTwoOf S X) :
    IsSylowTwoOf (S.map Φ) (X.map Φ) := by
  refine ⟨Subgroup.map_mono h.1, ?_, ?_⟩
  · exact h.2.1.of_equiv (Subgroup.equivMapOfInjective S Φ hΦ)
  · have e : ∀ (A B : Subgroup D), (A.subgroupOf B).index = A.relIndex B := fun _ _ => rfl
    have e' : ∀ (A B : Subgroup H), (A.subgroupOf B).index = A.relIndex B := fun _ _ => rfl
    have := h.2.2
    rw [e] at this
    rw [e', Subgroup.relIndex_map_map_of_injective S X hΦ]
    exact this

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_sp4_model (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (θ : StatedSp 2 K →* E),
      Function.Injective θ ∧ θ.range = Gp ∧ Gp ⊓ M₁ = (Q2 K 0).map θ ∧
        Gp ⊓ M₂ = (Q2 K 1).map θ := by
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .Sp4) hyp.toHypF_4_4g
  have hK : Nat.card marking.field = 2 ^ f := by
    have := marking.field_card
    simpa using this
  haveI : CharP marking.field 2 := burnsideF4gSp_charP_of_card hK
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have hinj : Function.Injective marking.transport := by
    refine (injective_iff_map_eq_one marking.transport).2 fun a ha => ?_
    have h3 := (burnsideF4f_transport_eq_one_iff marking a).1 ha
    exact Subtype.ext (burnsideF4gSpInv_scalar_eq_one h3 a.2)
  have hsurj := burnsideF4f_transport_surjective marking
  have keyS : ∀ (S : Set (Fin 2 ⊕ Fin 2))
      (W : Submodule marking.field (Fin 2 ⊕ Fin 2 → marking.field))
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) marking.field),
      (∀ v, v ∈ coordinateSpace S ↔ v ∈ W) →
      ((∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ coordinateSpace S ↔
          v ∈ coordinateSpace S) ↔
        ∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ W ↔ v ∈ W) := by
    intro S W A hS
    simp only [hS]
  have key : ∀ b : Bool, nativeParabolic .Sp4 (2 ^ f) marking.field marking.basis b =
      Q2 marking.field (if b then 1 else 0) := by
    intro b
    rw [hbasis]
    ext g
    have h1 : g ∈ nativeParabolic .Sp4 (2 ^ f) marking.field 1 b ↔
        (g : GL (Coord .Sp4) marking.field) ∈ rawStabilizer ((fun vector =>
            ((1 : GL (Coord .Sp4) marking.field) : Matrix (Coord .Sp4) (Coord .Sp4)
              marking.field).mulVec vector) ''
          coordinateSpace (if b then flagTwo .Sp4 else flagOne .Sp4 : Set (Coord .Sp4))) :=
      Iff.rfl
    rw [h1, burnsideF4gSp_mem_rawStabilizer, burnsideF4gSp_image_one, Q2]
    refine Iff.trans ?_
      (burnsideF4gSp_mem_stabilizer_iff (r := 2) (K := marking.field) _ g).symm
    cases b
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).1)
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).2)
  let θ : StatedSp 2 marking.field →* E := Gp.subtype.comp marking.transport
  have hθinj : Function.Injective θ := Gp.subtype_injective.comp hinj
  have hrange : θ.range = Gp := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (marking.transport y).2
    · intro hx
      obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  have hpar : ∀ (b : Bool) (M : Subgroup E), M.subgroupOf Gp = marking.parabolic b →
      Gp ⊓ M = (Q2 marking.field (if b then 1 else 0)).map θ := by
    intro b M hM
    have e1 : marking.parabolic b =
        (Q2 marking.field (if b then 1 else 0)).map marking.transport :=
      congrArg (Subgroup.map marking.transport) (key b)
    calc Gp ⊓ M = (M.subgroupOf Gp).map Gp.subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      _ = ((Q2 marking.field (if b then 1 else 0)).map marking.transport).map Gp.subtype := by
          rw [hM, e1]
      _ = (Q2 marking.field (if b then 1 else 0)).map θ := Subgroup.map_map _ _ _
  exact ⟨marking.field, inferInstance, inferInstance, inferInstance, θ, hθinj, hrange,
    by simpa using hpar false M₁ h1, by simpa using hpar true M₂ h2⟩

theorem burnsideF4m_sp4_gp (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) :
    ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp ∧
    Gp ⊓ Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) ≤ M₁ ⊓ M₂ ∧
    ∀ x ∈ Gp, x ≠ 1 → x * x = 1 →
      ∃ w : E, IsConj x w ∧ w ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧
        ((∀ n ∈ Gp, n * w = w * n → n ∈ M₁) ∨ (∀ n ∈ Gp, n * w = w * n → n ∈ M₂)) := by
  obtain ⟨K, _, _, _, θ, hθinj, hrange, hM₁, hM₂⟩ := burnsideF4m_sp4_model hyp
  have hB : Gp ⊓ (M₁ ⊓ M₂) = (borelSubgroup 2 K).map θ := by
    have e : Gp ⊓ (M₁ ⊓ M₂) = (Gp ⊓ M₁) ⊓ (Gp ⊓ M₂) := by
      ext y
      simp only [Subgroup.mem_inf]
      tauto
    rw [e, hM₁, hM₂, ← Subgroup.map_inf_eq _ _ _ hθinj, burnsideF4gSpInv_Q2_inf_eq_borel]
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (unipotent 2 K).map θ := by
    rw [hB, burnsideF4j_pCoreOf_map θ hθinj, burnsideF4gSpInv_pCoreOf_borel]
  have hZ : ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = (ctr (unipotent 2 K)).map θ := by
    rw [hS, burnsideF4j_ctr_map θ hθinj]
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := K) 2 2
    have hU0 : IsSylowTwoOf (unipotent 2 K) ⊤ :=
      hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
    have h := burnsideF4m_isSylowTwoOf_map_inj θ hθinj hU0
    rw [← MonoidHom.range_eq_map, hrange, ← hS] at h
    exact h
  ·
    rintro g ⟨hg, hgN⟩
    rw [← hrange] at hg
    obtain ⟨c, rfl⟩ := hg
    have hc : c ∈ Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have h1 := (Subgroup.mem_normalizer_iff.mp hgN) (θ u)
      rw [hS, Subgroup.mem_map_iff_mem hθinj,
        show θ c * θ u * (θ c)⁻¹ = θ (c * u * c⁻¹) by rw [map_mul, map_mul, map_inv],
        Subgroup.mem_map_iff_mem hθinj] at h1
      exact h1
    rw [normalizer_unipotent] at hc
    have hcB : θ c ∈ Gp ⊓ (M₁ ⊓ M₂) := by
      rw [hB]
      exact ⟨c, hc, rfl⟩
    exact hcB.2
  intro x hxG hx1 hx2
  have hcent : ∀ (y : StatedSp 2 K) (Q : Subgroup (StatedSp 2 K)),
      Subgroup.centralizer ({y} : Set (StatedSp 2 K)) ≤ Q →
      ∀ n ∈ Gp, n * θ y = θ y * n → n ∈ Q.map θ := by
    intro y Q hQ n hn hny
    rw [← hrange] at hn
    obtain ⟨c, rfl⟩ := hn
    refine ⟨c, hQ ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hθinj
    rw [map_mul, map_mul, hny]
  have hxr : x ∈ θ.range := hrange ▸ hxG
  obtain ⟨y, rfl⟩ := hxr
  have hy1 : y ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hy2 : y * y = 1 := hθinj (by rw [map_mul, hx2, map_one])
  have hmemM : ∀ (M : Subgroup E) (j : Fin 2), Gp ⊓ M = (Q2 K j).map θ →
      ∀ n, n ∈ (Q2 K j).map θ → n ∈ M := fun M j hM n hn => by
    rw [← hM] at hn
    exact hn.2
  rcases burnsideF4gSpInv_inv_exhaust y hy1 hy2 with h | h | h
  · refine ⟨θ (burnsideF4gSpInv_xl 1), θ.map_isConj h, ?_, Or.inl fun n hn hnw => ?_⟩
    · rw [hZ]
      exact ⟨_, burnsideF4gSpInv_xl_mem_ctr 1, rfl⟩
    · refine hmemM M₁ 0 hM₁ n (hcent _ _ ?_ n hn hnw)
      rw [burnsideF4gSpInv_centralizer_xl one_ne_zero]
      exact burnsideF4gSpInv_S1_le_Q2
  · refine ⟨θ (burnsideF4gSpInv_xs 1), θ.map_isConj h, ?_, Or.inr fun n hn hnw => ?_⟩
    · rw [hZ]
      exact ⟨_, burnsideF4gSpInv_xs_mem_ctr 1, rfl⟩
    · exact hmemM M₂ 1 hM₂ n
        (hcent _ _ (burnsideF4gSpInv_centralizer_xs_le one_ne_zero) n hn hnw)
  · refine ⟨θ (burnsideF4gSpInv_xl 1 * burnsideF4gSpInv_xs 1), θ.map_isConj h, ?_,
      Or.inr fun n hn hnw => ?_⟩
    · rw [hZ]
      exact ⟨_, (ctr (unipotent 2 K)).mul_mem (burnsideF4gSpInv_xl_mem_ctr 1)
        (burnsideF4gSpInv_xs_mem_ctr 1), rfl⟩
    · exact hmemM M₂ 1 hM₂ n (hcent _ _ burnsideF4m_centralizer_mixed_le n hn hnw)

theorem burnsideF4m_centInput_Sp4_all (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) {x : E} (hxG : x ∈ Gp)
    (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    ∃ w : E, IsConj x w ∧
      (Subgroup.centralizer ({w} : Set E) ≤ M₁ ∨ Subgroup.centralizer ({w} : Set E) ≤ M₂) := by
  obtain ⟨hSyl, hN, hrep⟩ := burnsideF4m_sp4_gp hyp
  obtain ⟨w, hxw, hwZ, hC⟩ := hrep x hxG hx1 hx2
  refine ⟨w, hxw, ?_⟩
  rcases hC with hC | hC
  · exact Or.inl (burnsideF4m_centralizer_le_of_ctr hyp.toHypF_4_4g hSyl hN hwZ inf_le_left hC)
  · exact Or.inr (burnsideF4m_centralizer_le_of_ctr hyp.toHypF_4_4g hSyl hN hwZ inf_le_right hC)

end Sp4Gp

end CFSG.ASVolI
