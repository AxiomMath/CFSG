module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91Pts
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.RankThree.GF2n.Stroth80.Sec53aProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem card_QB_inf_Wt_of_data (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {m : ℕ} (hm : 2 ≤ m)
    (hVcard : Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1))
    (hVQB : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) = Nat.card Z ^ (2 * m)) :
    Nat.card ↥(QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ n := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZW : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hz, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm
  have hn_gt : 2 < n := hs.n_gt
  obtain ⟨K, hKf, hKfin, hch, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  letI := hKf
  letI := hKfin
  have hKZ : Nat.card K = Nat.card Z := hD.card
  have hK2 : 1 < Nat.card K := by
    rw [hKZ]
    have := hc.hyp.q4
    omega
  have hcard33 : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) :=
    (hc.card_of_3_3 hs.width (by omega) hs.noA2 (stroth_3_3 hc hs.width (by omega))).2
  have hE : Module.finrank K M₀.E = 2 * n := hD.finrank_E hs.width hK2
  have hB : M₀.B.Nondegenerate := modelB_nondegenerate M₀
  have hrefl : M₀.B.IsRefl := LinearMap.IsAlt.isRefl (fun e => M₀.alt e)
  obtain ⟨U, hUmem⟩ := hc.exists_submodule_inf_QB hs.width hcard33 hD
  let Vsub : Submodule K M₀.E := imgSub M₀ (Vt M (LB M Q B) B Z t) (hc.smul_mem_img_Vt hD t)
  let Wsub : Submodule K M₀.E :=
    imgSub M₀ (Wt Q (Vt M (LB M Q B) B Z t))
      (fun c e he => smul_mem_img_Wt M₀ hD.reg hVQ c he)
  have hVsub_mem : ∀ e, e ∈ Vsub ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun e => mem_imgSub
  have hWsub_mem : ∀ e, e ∈ Wsub ↔ e ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) :=
    fun e => mem_imgSub
  have hUorth : ∀ e ∈ U, ∀ f ∈ U, M₀.B e f = 0 := by
    intro e he f hf
    obtain ⟨x, hx, hxe⟩ := (hUmem e).mp he
    obtain ⟨y, hy, hyf⟩ := (hUmem f).mp hf
    have hxy : ⁅x, y⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      have hc1 := hc.inf_QB_elemAbelian.1.is_comm
      exact congrArg Subtype.val (hc1.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have h1 := M₀.comm_eq x hx.1 y hy.1
    rw [hxy, hD.reg.one] at h1
    simpa [hxe, hyf] using h1.symm
  have hUle : U ≤ M₀.B.orthogonal U := by
    intro e he f hf
    rw [M₀.B_comm, hUorth e he f hf, neg_zero]
  have hUdim : Module.finrank K U = n := by
    have hUcardImg : Nat.card ↥U = Nat.card (M₀.img (Q ⊓ QB B)) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun e => hUmem e)
    have hQcard : Nat.card ↥(Q ⊓ QB B) =
        Nat.card Z * Nat.card (M₀.img (Q ⊓ QB B)) :=
      M₀.card_eq inf_le_left (le_inf hc.Z_le_Q hc.Z_le_QB.1)
    have hUcard : Nat.card ↥U = Nat.card Z ^ n := by
      rw [hUcardImg]
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← hQcard, hcard33, pow_succ]; ring
    have h1 : Nat.card K ^ Module.finrank K U = Nat.card K ^ n := by
      rw [← Module.natCard_eq_pow_finrank, hUcard, hKZ]
    exact Nat.pow_right_injective hK2 h1
  have hUlag : M₀.B.orthogonal U = U := by
    refine (Submodule.eq_of_le_of_finrank_eq hUle ?_).symm
    have h1 := LinearMap.BilinForm.finrank_orthogonal hB U
    omega
  have hVdim : Module.finrank K Vsub = 2 * m := by
    have hVcardImg : Nat.card ↥Vsub = Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun e => (hVsub_mem e).symm)
    have hQcard : Nat.card ↥(Vt M (LB M Q B) B Z t) =
        Nat.card Z * Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) :=
      M₀.card_eq hVQ sec39_Z_le_Vt
    have hVcard' : Nat.card ↥Vsub = Nat.card Z ^ (2 * m) := by
      rw [hVcardImg]
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← hQcard, hVcard, pow_succ]; ring
    have h1 : Nat.card K ^ Module.finrank K Vsub = Nat.card K ^ (2 * m) := by
      rw [← Module.natCard_eq_pow_finrank, hVcard', hKZ]
    exact Nat.pow_right_injective hK2 h1
  have hWorth : Wsub = M₀.B.orthogonal Vsub := by
    ext e
    rw [hWsub_mem, mem_img_Wt_iff M₀ hD.reg hVQ]
    constructor
    · intro h f hf
      rw [M₀.B_comm, h f ((hVsub_mem f).mpr hf), neg_zero]
    · intro h f hf
      have := h f ((hVsub_mem f).mpr hf)
      rwa [M₀.B_comm, neg_eq_zero] at this
  have hUVdim : Module.finrank K ↥(U ⊓ Vsub) = 2 * m - 1 := by
    have hsetV : Vt M (LB M Q B) B Z t ⊓ QB B =
        (Q ⊓ QB B) ⊓ Vt M (LB M Q B) B Z t := by
      ext x
      constructor
      · rintro ⟨hx, hxB⟩
        exact ⟨⟨hVQ hx, hxB⟩, hx⟩
      · rintro ⟨⟨-, hxB⟩, hx⟩
        exact ⟨hx, hxB⟩
    have hinfimg : M₀.img ((Q ⊓ QB B) ⊓ Vt M (LB M Q B) B Z t) =
        M₀.img (Q ⊓ QB B) ⊓ M₀.img (Vt M (LB M Q B) B Z t) :=
      quadModel_img_inf M₀ (le_inf hc.Z_le_Q hc.Z_le_QB.1) sec39_Z_le_Vt inf_le_left hVQ
    have hset : ∀ e, e ∈ U ⊓ Vsub ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t ⊓ QB B) := by
      intro e
      rw [Submodule.mem_inf, hUmem, hVsub_mem, hsetV]
      constructor
      · rintro ⟨he1, he2⟩
        rw [hinfimg]
        exact ⟨he1, he2⟩
      · intro he
        rw [hinfimg] at he
        exact ⟨he.1, he.2⟩
    have hcardImg : Nat.card (M₀.img (Vt M (LB M Q B) B Z t ⊓ QB B)) =
        Nat.card Z ^ (2 * m - 1) := by
      have h1 : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) =
          Nat.card Z * Nat.card (M₀.img (Vt M (LB M Q B) B Z t ⊓ QB B)) :=
        M₀.card_eq ((inf_le_left : Vt M (LB M Q B) B Z t ⊓ QB B ≤ _).trans hVQ)
          (le_inf sec39_Z_le_Vt hc.Z_le_QB.1)
      rw [hVQB] at h1
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← h1, ← pow_succ', show 2 * m - 1 + 1 = 2 * m by omega]
    have hUVcard : Nat.card ↥(U ⊓ Vsub) = Nat.card Z ^ (2 * m - 1) :=
      (Nat.card_congr (Equiv.subtypeEquivRight fun e => hset e)).trans hcardImg
    have h2 : Nat.card ↥(U ⊓ Vsub) = Nat.card K ^ (2 * m - 1) := by
      rw [hUVcard, hKZ]
    have h1 : Nat.card K ^ Module.finrank K ↥(U ⊓ Vsub) = Nat.card K ^ (2 * m - 1) := by
      conv_lhs => rw [← Module.natCard_eq_pow_finrank]
      exact h2
    exact Nat.pow_right_injective hK2 h1
  have hWdim : Module.finrank K Wsub = 2 * n - 2 * m := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal hB Vsub
    rw [← hWorth] at h1
    omega
  have horthsup : M₀.B.orthogonal (U ⊔ Wsub) = U ⊓ Vsub := by
    have hsup : M₀.B.orthogonal (U ⊔ Wsub) = M₀.B.orthogonal U ⊓ M₀.B.orthogonal Wsub := by
      ext w
      simp only [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
      constructor
      · intro h
        exact ⟨fun u hu => h u (Submodule.mem_sup_left hu),
          fun u hu => h u (Submodule.mem_sup_right hu)⟩
      · rintro ⟨h, h'⟩ u hu
        obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hu
        rw [map_add, LinearMap.add_apply, h a ha, h' a' ha', add_zero]
    rw [hsup, hUlag, hWorth, LinearMap.BilinForm.orthogonal_orthogonal hB hrefl Vsub]
  have hUWdim : Module.finrank K ↥(U ⊓ Wsub) = n - 1 := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq U Wsub
    have e2 := LinearMap.BilinForm.finrank_orthogonal hB (U ⊔ Wsub)
    rw [horthsup, hUVdim] at e2
    have e3 : Module.finrank K ↥(U ⊔ Wsub) ≤ Module.finrank K M₀.E := Submodule.finrank_le _
    omega
  have hUWcard : Nat.card ↥(U ⊓ Wsub) = Nat.card Z ^ (n - 1) := by
    have h2 : Nat.card ↥(U ⊓ Wsub) = Nat.card K ^ (n - 1) := by
      conv_lhs => rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(U ⊓ Wsub))]
      rw [hUWdim]
    rwa [hKZ] at h2
  have hImgEq : M₀.img (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) =
      (U ⊓ Wsub).toAddSubgroup := by
    have hinfimg := quadModel_img_inf M₀
      (S := Q ⊓ QB B) (T := Wt Q (Vt M (LB M Q B) B Z t))
      (le_inf hc.Z_le_Q hc.Z_le_QB.1) hZW inf_le_left inf_le_left
    have hset : (Q ⊓ QB B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) =
        QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) := by
      ext x
      constructor
      · rintro ⟨⟨-, hx⟩, hw⟩
        exact ⟨hx, hw⟩
      · rintro ⟨hx, hw⟩
        exact ⟨⟨(inf_le_left : Wt Q _ ≤ Q) hw, hx⟩, hw⟩
    rw [hset] at hinfimg
    rw [hinfimg]
    ext e
    constructor
    · rintro ⟨he1, he2⟩
      exact ⟨(hUmem e).mpr he1, (hWsub_mem e).mpr he2⟩
    · rintro ⟨he1, he2⟩
      exact ⟨(hUmem e).mp he1, (hWsub_mem e).mp he2⟩
  have hWcard : Nat.card ↥(QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) =
      Nat.card Z * Nat.card ↥(U ⊓ Wsub) := by
    have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
    have h1 := M₀.card_eq (S := QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t))
      (inf_le_right.trans hWQ) (le_inf hc.Z_le_QB.1 hZW)
    rw [h1, hImgEq]
    rfl
  have hn1 : 1 ≤ n := by have := hs.n_gt; omega
  rw [hWcard, hUWcard]
  rw [← pow_succ', show n - 1 + 1 = n by omega]


end HS9


theorem step91OrderQB_of (h34 : Stroth34Statement) : Step91OrderQBStatement := by
  intro G _ _ M Q Z B hc n t hs V W hV hW
  subst hV hW
  have hs5 := hs.toSec5
  obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, u, P⟩ := HS9.exists_pts91 h34 hs
  haveI := hn
  have hQB := HS9.card_QB_inf_Wt_of_data hc hs5 (m := 2) le_rfl hs.card_V
    (HS9.card_Vt_inf_QB_plus4 P)
  have hQQB : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) :=
    (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.2.2
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hset : Q ⊓ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) =
      QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) := by
    ext x
    constructor
    · rintro ⟨⟨-, hx⟩, hxW⟩
      exact ⟨hx, hxW⟩
    · rintro ⟨hx, hxW⟩
      exact ⟨⟨hWQ hxW, hx⟩, hxW⟩
  rw [hset, hQB, hQQB]
  ring

end CFSG.RankThree.GF2n.Stroth80
