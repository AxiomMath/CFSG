module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Eichler
public import CFSG.RankThree.GF2n.Stroth80.Sec310Perp
public import CFSG.RankThree.GF2n.Stroth80.Sec310MatRep
public import CFSG.RankThree.GF2n.Stroth80.Sec310ElCount

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.centralizer_inf_QB_le (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀) {x : G} (hx : x ∈ QB B)
    (hxc : ∀ r ∈ Q ⊓ QB B, x * r = r * x) : x ∈ Q := by
  classical
  obtain ⟨n₀, h1, h2⟩ := hc.exists_swap
  obtain ⟨W, hWmem, hWo⟩ := hc.img_inf_QB_lagrangian hw hn hno h
  have hLZ : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hx'Q : n₀⁻¹ * x * n₀ ∈ Q := mem_conjSubgroup.mp (h1 ▸ hx)
  have hswap : ∀ r ∈ Q ⊓ QB B, n₀ * r * n₀⁻¹ ∈ Q ⊓ QB B := by
    intro r hr
    refine ⟨?_, ?_⟩
    · have e : n₀ * r * n₀⁻¹ ∈ conjSubgroup n₀ (QB B) := by
        rw [mem_conjSubgroup, show n₀⁻¹ * (n₀ * r * n₀⁻¹) * n₀ = r by group]
        exact hr.2
      rwa [h2] at e
    · have e : n₀ * r * n₀⁻¹ ∈ conjSubgroup n₀ Q := by
        rw [mem_conjSubgroup, show n₀⁻¹ * (n₀ * r * n₀⁻¹) * n₀ = r by group]
        exact hr.1
      rwa [h1] at e
  have hx'c : ∀ r ∈ Q ⊓ QB B, (n₀⁻¹ * x * n₀) * r = r * (n₀⁻¹ * x * n₀) := by
    intro r hr
    have e := hxc _ (hswap r hr)
    calc (n₀⁻¹ * x * n₀) * r = n₀⁻¹ * (x * (n₀ * r * n₀⁻¹)) * n₀ := by group
      _ = n₀⁻¹ * ((n₀ * r * n₀⁻¹) * x) * n₀ := by rw [e]
      _ = r * (n₀⁻¹ * x * n₀) := by group
  have hmem : M₀.π (n₀⁻¹ * x * n₀) ∈ W := by
    refine hWo _ fun u hu => ?_
    obtain ⟨r, hrL, hrQ, rfl⟩ := (hWmem u).mpr hu
    exact (Tim79.QuadModel.comm_iff_B M₀ h.reg hx'Q hrQ).mp (hx'c r hrL)
  have hx'L : n₀⁻¹ * x * n₀ ∈ Q ⊓ QB B := (M₀.mem_img_iff hLZ hx'Q).mp ((hWmem _).mpr hmem)
  have e : n₀ * (n₀⁻¹ * x * n₀) * n₀⁻¹ ∈ conjSubgroup n₀ (QB B) := by
    rw [mem_conjSubgroup, show n₀⁻¹ * (n₀ * (n₀⁻¹ * x * n₀) * n₀⁻¹) * n₀ = n₀⁻¹ * x * n₀ by group]
    exact hx'L.2
  rw [h2, show n₀ * (n₀⁻¹ * x * n₀) * n₀⁻¹ = x by group] at e
  exact e

theorem Ctx.A0_le_Q (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀) :
    A0 Q Z B ≤ Q := fun _ ha =>
  hc.centralizer_inf_QB_le hw hn hno h ha.1.1 fun _ hr => hc.A0_comm ha hr


theorem Ctx.exists_elation_action (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (hcardL : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1))
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (h : GlobalModelData M Q Z γ M₀) :
    ∃ (W : Submodule K M₀.E) (b : W) (θ : ↥(LB M Q B) →* (W ≃ₗ[K] W)),
      (∀ v, v ∈ W ↔ v ∈ M₀.img (Q ⊓ QB B)) ∧ b ≠ 0 ∧
      (∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • (b : M₀.E)) ∧
      (∀ g, θ g b = b) ∧ (∀ (g : ↥(LB M Q B)) (u : W), ∃ c : K, θ g u = u + c • b) ∧
      (∀ g : ↥(LB M Q B), θ g = 1 ↔ (g : G) ∈ Q) ∧ Module.finrank K W = n ∧
      (∀ (g : ↥(LB M Q B)) (y : G) (hyL : y ∈ Q ⊓ QB B) (hyW : M₀.π y ∈ W),
        ((θ g ⟨M₀.π y, hyW⟩ : W) : M₀.E) = M₀.π y ↔ ⁅(g : G), y⁆ ∈ Z) ∧
      ∀ (g : ↥(LB M Q B)) (S : M₀.E ≃ₗ[K] M₀.E),
        (∀ x ∈ Q, M₀.π ((g : G) * x * (g : G)⁻¹) = S (M₀.π x)) →
          ∀ w : W, ((θ g w : W) : M₀.E) = S (w : M₀.E) := by
  classical
  obtain ⟨W, hW⟩ := hc.exists_submodule_inf_QB hw hcardL h
  obtain ⟨φ, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨b, hb0, -, hB, -, -⟩ := hc.dictB h
  have hLZ : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hBL : B ≤ Q ⊓ QB B := le_inf hc.le hc.B_le_QB
  have hbimg : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul K b).symm⟩
  have hbW : b ∈ W := (hW b).mpr (M₀.img_mono hBL hbimg)
  let φL : ↥(LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp (Subgroup.inclusion hc.LB_le_H0)
  have hφL : ∀ (r : ↥(LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((r : G) * x * (r : G)⁻¹) = φL r (M₀.π x) := fun r x hx =>
    hφπ (Subgroup.inclusion hc.LB_le_H0 r) x hx
  have hrM : ∀ r : ↥(LB M Q B), (r : G) ∈ M := fun r => hc.LB_le_M r.2
  have hrQ : ∀ (r : ↥(LB M Q B)) (x : G), x ∈ Q → (r : G) * x * (r : G)⁻¹ ∈ Q := fun r x hx =>
    (hc.conj_mem_Q_of_mem_M (hrM r)).1 x hx
  have hD : ∀ (r : ↥(LB M Q B)), ∀ e ∈ M₀.img (Q ⊓ QB B), ∃ c : K, φL r e - e = c • b :=
    fun r e he => (hc.LB_act_flag hw hn hno h hB r.2 (T := (φL r : M₀.E →ₗ[K] M₀.E))
      (hφL r)).2.1 e he
  have hφb : ∀ r : ↥(LB M Q B), φL r b = b := by
    intro r
    obtain ⟨u, huB, huQ, hu⟩ := hbimg
    rw [← hu, ← hφL r u huQ]
    exact (M₀.comm_mem_iff huQ (hrQ r u huQ)).mp (hc.comm_B_mem_Z r.2 huB)
  have hinv : ∀ (r : ↥(LB M Q B)), ∀ w ∈ W, φL r w ∈ W := by
    intro r w hw'
    obtain ⟨c, hcw⟩ := hD r w ((hW w).mp hw')
    have e : φL r w = w + c • b := by rw [← hcw]; abel
    rw [e]
    exact W.add_mem hw' (W.smul_mem c hbW)
  let θ := actionOnSubspace φL W hinv
  have hθ : ∀ (r : ↥(LB M Q B)) (w : W), ((θ r w : W) : M₀.E) = φL r (w : M₀.E) :=
    fun r w => actionOnSubspace_apply φL W hinv r w
  refine ⟨W, ⟨b, hbW⟩, θ, hW, fun h0 => hb0 (congrArg Subtype.val h0), hB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    apply Subtype.ext
    rw [hθ]
    exact hφb g
  · intro g u
    obtain ⟨c, hcu⟩ := hD g u ((hW u).mp u.2)
    refine ⟨c, Subtype.ext ?_⟩
    rw [hθ]
    show φL g (u : M₀.E) = (u : M₀.E) + c • b
    rw [← hcu]
    abel
  · intro g
    constructor
    · intro hg
      obtain ⟨s, hs, y, hyQ, hgsy⟩ := hc.exists_mul_of_mem_LB g.2
      have hsH : s ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) := hc.QB_inf_M_eq ▸ hs
      have hsA : s ∈ A0 Q Z B := by
        refine ⟨hsH, fun r hr => ?_⟩
        have hrQ' : r ∈ Q := hr.1
        have hrW : M₀.π r ∈ W := (hW _).mpr (M₀.pi_mem_img hr hrQ')
        have h1 : φL g (M₀.π r) = M₀.π r := by
          have := congrArg (fun f : W ≃ₗ[K] W => ((f ⟨M₀.π r, hrW⟩ : W) : M₀.E)) hg
          simpa [hθ] using this
        have hsQ : s * r * s⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hs.2).1 r hrQ'
        have hyrQ : y * r * y⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hyQ hrQ') (Q.inv_mem hyQ)
        have h2 : M₀.π ((g : G) * r * (g : G)⁻¹) = M₀.π (s * r * s⁻¹) := by
          have e : (g : G) * r * (g : G)⁻¹ = s * (y * r * y⁻¹) * s⁻¹ := by rw [hgsy]; group
          have hsyr : s * (y * r * y⁻¹) * s⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hs.2).1 _ hyrQ
          rw [e]
          have hH : s ∈ H0 M Z := ⟨hs.2, hsH.2⟩
          have h3 := hφπ ⟨s, hH⟩ (y * r * y⁻¹) hyrQ
          have h4 := hφπ ⟨s, hH⟩ r hrQ'
          simp only at h3 h4
          rw [h3, h4, Tim79.QuadModel.pi_conj_self (M₀ := M₀) hyQ hrQ']
        rw [← hφL g r hrQ', h2] at h1
        exact (M₀.comm_mem_iff hrQ' hsQ).mpr h1
      have hsQ := hc.A0_le_Q hw hn hno h hsA
      rw [hgsy]
      exact Q.mul_mem hsQ hyQ
    · intro hgQ
      apply LinearEquiv.ext
      intro w
      apply Subtype.ext
      rw [hθ]
      show φL g (w : M₀.E) = (w : M₀.E)
      obtain ⟨x, -, hxQ, hx⟩ := (hW _).mp w.2
      rw [← hx, ← hφL g x hxQ]
      exact Tim79.QuadModel.pi_conj_self (M₀ := M₀) hgQ hxQ
  · have hXQ : Q ⊓ QB B ≤ Q := inf_le_left
    have hcardX : Nat.card ↥(Q ⊓ QB B) = Nat.card Z * Nat.card (M₀.img (Q ⊓ QB B)) :=
      M₀.card_eq hXQ hLZ
    have hKZ : Nat.card K = Nat.card Z := h.card
    have hK : 1 < Nat.card K := by
      rw [hKZ]
      have := hc.hyp.q4
      omega
    have himg : Nat.card (M₀.img (Q ⊓ QB B)) = Nat.card K ^ n := by
      rw [hKZ]
      have h1 : Nat.card Z * Nat.card (M₀.img (Q ⊓ QB B)) = Nat.card Z * Nat.card Z ^ n := by
        rw [← hcardX, hcardL, pow_succ, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    have hWcard : Nat.card W = Nat.card (M₀.img (Q ⊓ QB B)) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => hW v)
    rw [Module.natCard_eq_pow_finrank (K := K), himg] at hWcard
    exact Nat.pow_right_injective hK hWcard
  · intro g y hyL hyW
    have hyQ : y ∈ Q := hyL.1
    rw [hθ]
    show φL g (M₀.π y) = M₀.π y ↔ _
    rw [← hφL g y hyQ]
    exact (M₀.comm_mem_iff hyQ (hrQ g y hyQ)).symm
  · intro g S hS w
    rw [hθ]
    obtain ⟨x, hxQ, hx⟩ := M₀.π_surj (w : M₀.E)
    rw [← hx, ← hS x hxQ, hφL g x hxQ]


theorem Ctx.elation_package (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B))
    (hcardLB : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1))
    (hcardL : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1))
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (h : GlobalModelData M Q Z γ M₀) {Y : Subgroup G} (hBY : B ≤ Y) (hYL : Y ≤ Q ⊓ QB B)
    (hY : ∀ (c : K) (e : M₀.E), e ∈ M₀.img Y → c • e ∈ M₀.img Y) :
    ∃ (b : M₀.E) (hbY : b ∈ imgSub M₀ Y hY), b ≠ 0 ∧
      (∀ v, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) ∧
      (∀ l ∈ LB M Q B, ∀ S : M₀.E ≃ₗ[K] M₀.E,
        (∀ x ∈ Q, M₀.π (l * x * l⁻¹) = S (M₀.π x)) →
          S b = b ∧ ∀ e ∈ imgSub M₀ Y hY, ∃ s : K, S e - e = s • b) ∧
      (∀ f : Module.Dual K (imgSub M₀ Y hY), f ⟨b, hbY⟩ = 0 →
        ∃ l ∈ LB M Q B, ∀ S : M₀.E ≃ₗ[K] M₀.E,
          (∀ x ∈ Q, M₀.π (l * x * l⁻¹) = S (M₀.π x)) →
            ∀ y : imgSub M₀ Y hY, S (y : M₀.E) = (y : M₀.E) + f y • b) ∧
      (∀ T : Subgroup G, (∀ x, x ∈ T ↔ x ∈ LB M Q B ∧ ∀ y ∈ Y, ⁅x, y⁆ ∈ Z) →
        Nat.card (LB M Q B) =
          Nat.card T * Nat.card K ^ (Module.finrank K (imgSub M₀ Y hY) - 1)) := by
  classical
  obtain ⟨W, b, θ, hW, hb0, hB, hfix, hel, hker, hfr, hcomm, hSθ⟩ :=
    hc.exists_elation_action hw hn hno hcardL h
  have hbY : (b : M₀.E) ∈ imgSub M₀ Y hY :=
    mem_imgSub.mpr (M₀.img_mono hBY ((hB b).mpr ⟨1, (one_smul K _).symm⟩))
  have hYW : ∀ e ∈ imgSub M₀ Y hY, e ∈ W := fun e he =>
    (hW e).mpr (M₀.img_mono hYL (mem_imgSub.mp he))
  have hb0' : (b : M₀.E) ≠ 0 := fun h0 => hb0 (Subtype.ext h0)
  have hQLB : Q ≤ LB M Q B := sec39_Q_le_LB
  have hθker : θ.ker = Q.subgroupOf (LB M Q B) := by
    ext g
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hKZ : Nat.card K = Nat.card Z := h.card
  have hcard : Nat.card (LB M Q B) = Nat.card θ.ker * Nat.card K ^ (Module.finrank K W - 1) := by
    rw [hθker, hfr, hcardLB, hKZ]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQLB).toEquiv).symm
  have hle : imgSub M₀ Y hY ≤ W := fun e he => hYW e he
  let Ysub : Submodule K W := Submodule.comap W.subtype (imgSub M₀ Y hY)
  let eY : Ysub ≃ₗ[K] imgSub M₀ Y hY := Submodule.comapSubtypeEquivOfLe hle
  have hbYsub : b ∈ Ysub := hbY
  refine ⟨b, hbY, hb0', hB, ?_, ?_, ?_⟩
  · intro l hl S hS
    have hSb := hSθ ⟨l, hl⟩ S hS
    refine ⟨?_, fun e he => ?_⟩
    · rw [← hSb b, hfix]
    · obtain ⟨c, hc'⟩ := hel ⟨l, hl⟩ ⟨e, hYW e he⟩
      refine ⟨c, ?_⟩
      have h1 := congrArg Subtype.val hc'
      rw [hSb] at h1
      have h2 : S e = e + c • (b : M₀.E) := h1
      rw [h2]
      abel
  · intro f hf
    let f' : Module.Dual K Ysub := f.comp eY.toLinearMap
    have hf' : f' ⟨b, hbYsub⟩ = 0 := hf
    obtain ⟨g, hg⟩ := elation_exists hb0 θ hfix hel hcard Ysub hbYsub f' hf'
    refine ⟨(g : G), g.2, fun S hS y => ?_⟩
    have h1 := hg ⟨⟨y, hYW y y.2⟩, y.2⟩
    have h2 := congrArg Subtype.val h1
    rw [hSθ g S hS] at h2
    exact h2
  · intro T hT
    have hTL : T ≤ LB M Q B := fun x hx => ((hT x).mp hx).1
    have hS : ∀ g : ↥(LB M Q B), g ∈ T.subgroupOf (LB M Q B) ↔ ∀ y ∈ Ysub, θ g y = y := by
      intro g
      rw [Subgroup.mem_subgroupOf, hT]
      constructor
      · rintro ⟨-, hg⟩ ⟨e, he⟩ hye
        have hye' : e ∈ imgSub M₀ Y hY := hye
        obtain ⟨y, hyY, hyQ, rfl⟩ := mem_imgSub.mp hye'
        exact Subtype.ext ((hcomm g y (hYL hyY) he).mpr (hg y hyY))
      · intro hg
        refine ⟨g.2, fun y hy => ?_⟩
        have hyW : M₀.π y ∈ W := hYW _ (mem_imgSub.mpr (M₀.pi_mem_img hy (hYL hy).1))
        have hyY : M₀.π y ∈ imgSub M₀ Y hY := mem_imgSub.mpr (M₀.pi_mem_img hy (hYL hy).1)
        have h1 := hg ⟨M₀.π y, hyW⟩ hyY
        exact (hcomm g y (hYL hy) hyW).mp (congrArg Subtype.val h1)
    have key := elation_count hb0 θ hfix hel hcard Ysub hbYsub (T.subgroupOf (LB M Q B)) hS
    rw [key]
    congr 1
    · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
    · rw [eY.finrank_eq]

end CFSG.RankThree.GF2n.Stroth80
