module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveNbr
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInnAll
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveNbrBasic
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveBstar
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveBasis
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveStdSub
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveSl3Facts

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)

include h

theorem innerDiag_nb {N : Subgroup G}
    (hN : GGNbr p B x (dPrime x φ₁ φ₂) (sl3four.map φ₁) (bElt φ₁ φ₂) N)
    (hL₁ : sl3four.map φ₁ ≤ N) (hK₁ : sl3four.map φ₂ ≤ N) : GGInnerDiagOn Bs N := by
  have hst : LargeEvenStandardType p B x L := h.cfg.1.2.2.2.2.2.2.2
  have hnb := hst.2.2.1 (bElt φ₁ φ₂) N (isNeighborOf_of_ggNbr (stdSub_lb h) hN)
  have hnorm : Bs ≤ Subgroup.normalizer (N : Set G) := by
    rw [bs_eq h]
    exact hnb.1
  have hmark : LargeEvenMarking ↥N fun _ _ _ _ _ _ => True :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) hnb.2
  refine ggInnerDiagOn_of_inner hmark hnorm ?_
  have hbN : bElt φ₁ φ₂ ∈ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_nbr hN hn)
  obtain ⟨e, he0, he1, he2, he3, -, -, hcl, -⟩ := exists_bsBasis h
  have hdiv := omega_div_mem_sl3four
  have ha_memL : vElt φ₁ * (uElt φ₂)⁻¹ ∈ sl3four.map φ₁ := by
    have heq : vElt φ₁ * (uElt φ₂)⁻¹ = φ₁ (omegaBlock 5 0 * (omegaBlock 5 2)⁻¹) := by
      rw [uElt_eq h, map_mul, map_inv]
      rfl
    rw [heq]
    exact Subgroup.mem_map.mpr ⟨_, hdiv.1, rfl⟩
  have ha'_memL : uElt φ₂ * (φ₁ (omegaBlock 5 4))⁻¹ ∈ sl3four.map φ₁ := by
    have heq : uElt φ₂ * (φ₁ (omegaBlock 5 4))⁻¹ = φ₁ (omegaBlock 5 2 * (omegaBlock 5 4)⁻¹) := by
      rw [uElt_eq h, map_mul, map_inv]
      rfl
    rw [heq]
    exact Subgroup.mem_map.mpr ⟨_, hdiv.2, rfl⟩
  have ha''_memK : φ₁ (omegaBlock 5 4) * (wElt φ₂)⁻¹ ∈ sl3four.map φ₂ := by
    have heq : φ₁ (omegaBlock 5 4) * (wElt φ₂)⁻¹ = φ₂ (omegaBlock 5 2 * (omegaBlock 5 4)⁻¹) := by
      rw [phi1_omega4_eq h, map_mul, map_inv]
      rfl
    rw [heq]
    exact Subgroup.mem_map.mpr ⟨_, hdiv.2, rfl⟩
  have haN : vElt φ₁ * (uElt φ₂)⁻¹ ∈ N := hL₁ ha_memL
  have ha'N : uElt φ₂ * (φ₁ (omegaBlock 5 4))⁻¹ ∈ N := hL₁ ha'_memL
  have ha''N : φ₁ (omegaBlock 5 4) * (wElt φ₂)⁻¹ ∈ N := hK₁ ha''_memK
  have hkey : vElt φ₁ * uElt φ₂ * φ₁ (omegaBlock 5 4) =
      (vElt φ₁ * (uElt φ₂)⁻¹) * (uElt φ₂ * (φ₁ (omegaBlock 5 4))⁻¹) ^ 2 := by
    let V : ↥Bs := ⟨vElt φ₁, h.vElt_mem⟩
    let U1 : ↥Bs := ⟨uElt φ₂, h.uElt_mem⟩
    let U2 : ↥Bs := ⟨φ₁ (omegaBlock 5 4), by rw [← he2]; exact (e 2).2⟩
    have hU2pow : U2 ^ 3 = 1 := by
      apply Subtype.ext
      show (φ₁ (omegaBlock 5 4)) ^ 3 = (1 : G)
      rw [← map_pow, omegaBlock_pow_three, map_one]
    have hsub : V * U1 * U2 = V * U1⁻¹ * (U1 * U2⁻¹) ^ 2 := by
      have hcomm : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
        Subtype.ext (h.basic.1 (a : G) a.2 (b : G) b.2)
      have h3 : U2⁻¹ ^ 2 = U2 := by
        rw [inv_pow]
        have h2 : U2 ^ 2 = U2⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← pow_succ]
          exact hU2pow
        rw [h2, inv_inv]
      have hsq : (U1 * U2⁻¹) ^ 2 = U1 ^ 2 * (U2⁻¹) ^ 2 := by
        rw [pow_two, pow_two, pow_two]
        calc (U1 * U2⁻¹) * (U1 * U2⁻¹) = U1 * (U2⁻¹ * U1) * U2⁻¹ := by group
          _ = U1 * (U1 * U2⁻¹) * U2⁻¹ := by rw [hcomm (U2⁻¹) U1]
          _ = U1 * U1 * (U2⁻¹ * U2⁻¹) := by group
      rw [hsq]
      conv_lhs => rw [← h3]
      group
    simpa [V, U1, U2] using congrArg Subtype.val hsub
  have hw_eq : wElt φ₂ =
      (vElt φ₁ * (uElt φ₂)⁻¹ * (uElt φ₂ * (φ₁ (omegaBlock 5 4))⁻¹) ^ 2)⁻¹ * bElt φ₁ φ₂ := by
    rw [bElt_eq h, hkey]
    group
  let inn : G → Prop := fun c => ∃ n ∈ N, ∀ l ∈ N, c⁻¹ * l * c = n⁻¹ * l * n
  have hinn_one : inn 1 := ⟨1, N.one_mem, fun l _ => by group⟩
  have hinn_N : ∀ n ∈ N, inn n := fun n hn => ⟨n, hn, fun l _ => rfl⟩
  have hinn_mul : ∀ a b : G, inn a → inn b → inn (a * b) := by
    rintro a b ⟨n, hnN, hn⟩ ⟨m, hmN, hm⟩
    refine ⟨n * m, N.mul_mem hnN hmN, fun l hl => ?_⟩
    have hnl : n⁻¹ * l * n ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hnN) hl) hnN
    calc (a * b)⁻¹ * l * (a * b)
        = b⁻¹ * (a⁻¹ * l * a) * b := by group
      _ = b⁻¹ * (n⁻¹ * l * n) * b := by rw [hn l hl]
      _ = m⁻¹ * (n⁻¹ * l * n) * m := by rw [hm (n⁻¹ * l * n) hnl]
      _ = (n * m)⁻¹ * l * (n * m) := by group
  have hinn_inv : ∀ a : G, inn a → inn a⁻¹ := by
    rintro a ⟨n, hnN, hn⟩
    refine ⟨n⁻¹, N.inv_mem hnN, fun l hl => ?_⟩
    have h1 : a * l * a⁻¹ = n * l * n⁻¹ := by
      have h2 : a⁻¹ * (n * l * n⁻¹) * a = l := by
        have h3 := hn (n * l * n⁻¹) (N.mul_mem (N.mul_mem hnN hl) (N.inv_mem hnN))
        rw [h3]; group
      calc a * l * a⁻¹ = a * (a⁻¹ * (n * l * n⁻¹) * a) * a⁻¹ := by rw [h2]
        _ = n * l * n⁻¹ := by group
    show (a⁻¹)⁻¹ * l * a⁻¹ = (n⁻¹)⁻¹ * l * n⁻¹
    rw [inv_inv, inv_inv]
    exact h1
  have hinn_b : inn (bElt φ₁ φ₂) := by
    refine ⟨1, N.one_mem, fun l hl => ?_⟩
    have hbl : l * bElt φ₁ φ₂ = bElt φ₁ φ₂ * l :=
      Subgroup.mem_centralizer_iff.mp hbN l hl
    show (bElt φ₁ φ₂)⁻¹ * l * bElt φ₁ φ₂ = (1 : G)⁻¹ * l * 1
    rw [inv_one, one_mul, mul_one]
    calc (bElt φ₁ φ₂)⁻¹ * l * bElt φ₁ φ₂
        = (bElt φ₁ φ₂)⁻¹ * (l * bElt φ₁ φ₂) := by group
      _ = (bElt φ₁ φ₂)⁻¹ * (bElt φ₁ φ₂ * l) := by rw [hbl]
      _ = l := by group
  have hinn_w : inn (wElt φ₂) := by
    have ha'2 : inn ((uElt φ₂ * (φ₁ (omegaBlock 5 4))⁻¹) ^ 2) := by
      rw [pow_two]
      exact hinn_mul _ _ (hinn_N _ ha'N) (hinn_N _ ha'N)
    have haa' : inn (vElt φ₁ * (uElt φ₂)⁻¹ *
        (uElt φ₂ * (φ₁ (omegaBlock 5 4))⁻¹) ^ 2) :=
      hinn_mul _ _ (hinn_N _ haN) ha'2
    rw [hw_eq]
    exact hinn_mul _ _ (hinn_inv _ haa') hinn_b
  have hinn_u2 : inn (φ₁ (omegaBlock 5 4)) := by
    have hu2_eq : φ₁ (omegaBlock 5 4) =
        (φ₁ (omegaBlock 5 4) * (wElt φ₂)⁻¹) * wElt φ₂ := by group
    rw [hu2_eq]
    exact hinn_mul _ _ (hinn_N _ ha''N) hinn_w
  have hinn_u1 : inn (uElt φ₂) := by
    have hu1_eq : uElt φ₂ =
        (uElt φ₂ * (φ₁ (omegaBlock 5 4))⁻¹) * φ₁ (omegaBlock 5 4) := by group
    rw [hu1_eq]
    exact hinn_mul _ _ (hinn_N _ ha'N) hinn_u2
  have hinn_v : inn (vElt φ₁) := by
    have hv_eq : vElt φ₁ = (vElt φ₁ * (uElt φ₂)⁻¹) * uElt φ₂ := by group
    rw [hv_eq]
    exact hinn_mul _ _ (hinn_N _ haN) hinn_u1
  have hgen : ∀ i : Fin 4, inn (e i : G) := by
    intro i
    fin_cases i
    · change inn (↑(e 0)); rw [he0]; exact hinn_v
    · change inn (↑(e 1)); rw [he1]; exact hinn_u1
    · change inn (↑(e 2)); rw [he2]; exact hinn_u2
    · change inn (↑(e 3)); rw [he3]; exact hinn_w
  intro c hc
  have hx : (⟨c, hc⟩ : ↥Bs) ∈ Subgroup.closure (Set.range e) := by
    rw [hcl]; exact Subgroup.mem_top _
  have hres : inn ((⟨c, hc⟩ : ↥Bs) : G) := by
    refine Subgroup.closure_induction
      (p := fun y (_ : y ∈ Subgroup.closure (Set.range e)) => inn (y : G)) ?_ ?_ ?_ ?_ hx
    · intro z hz
      obtain ⟨i, rfl⟩ := hz
      exact hgen i
    · exact hinn_one
    · intro y z _ _ ihy ihz
      exact hinn_mul (y : G) (z : G) ihy ihz
    · intro y _ ihy
      exact hinn_inv (y : G) ihy
  simpa using hres

end GGHalfCtx

end CFSG.StandardType

end
