module

public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.Quasithin.Background.HSecTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardCoreCent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.Quasithin.H13 CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16c11_v1_altCore_faithful {n : ℕ} (hn : 3 ≤ n) :
    (altCoreModel n).Faithful := by
  intro γ hγ
  apply Subtype.ext
  apply G64.symCore_faithful hn
  intro m hm
  exact hγ m hm

private theorem s16c11_v1_card_two_mul {X Y : Type} [Group X] [Group Y] {n : ℕ}
    (hn : 2 ≤ n) (hX : IsSym X n) (hY : UC22.IsAlt Y n) : Nat.card X = 2 * Nat.card Y := by
  obtain ⟨eX⟩ := hX
  obtain ⟨eY⟩ := hY
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_congr eX.toEquiv, Nat.card_congr eY.toEquiv,
    two_mul_nat_card_alternatingGroup]

private theorem s16c11_v1_normalizer_of_card_two_mul {W : Type} [CommGroup W] [Finite W]
    {L L₀ : Subgroup (MulAut W)} (hLL₀ : L ≤ L₀) (hcard : Nat.card ↥L₀ = 2 * Nat.card ↥L) :
    L₀ ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  have hrel : L.relIndex L₀ = 2 := by
    have h := Subgroup.relIndex_mul_card L L₀
    rw [inf_eq_left.mpr hLL₀, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hnormal : (L.subgroupOf L₀).Normal := Subgroup.normal_of_index_eq_two hrel
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hLL₀).1 hnormal

private theorem s16c11_v1_coreAct_injective {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (G6.coreAct n) := by
  rw [injective_iff_map_eq_one]
  intro σ h
  refine G64.symCore_faithful hn σ fun m hm => ?_
  have h2 : (G6.coreAct n σ) ⟨m, hm⟩ = ⟨m, hm⟩ := by rw [h]; rfl
  have h3 : G6.permAct n σ m = m := congrArg Subtype.val h2
  exact Subgroup.mem_bot.2 (mul_inv_eq_one.2 h3)

theorem s16c11_v1_symCore_self (n : ℕ) :
    (G64.symCoreModel n).Realizes (V := ↥((G64.symCoreModel n).sec))
      (G6.coreAct n).range ⊤ ⊥ := by
  let D := G64.symCoreModel n
  let N : Subgroup ↥D.sec := D.ker.subgroupOf D.sec
  have hN : N = ⊥ := Subgroup.bot_subgroupOf D.sec
  haveI : N.Normal := by rw [hN]; infer_instance
  refine ⟨(G6.coreAct n).rangeRestrict, MonoidHom.rangeRestrict_surjective _, bot_le, bot_le,
    (fun h u _ => Subgroup.mem_top (h.1 u)), (fun _ z hz => ?_),
    (fun γ m hm => ?_), (fun γ m hm => ?_), ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · exact G6.permAct_mem_coreMod γ (show m ∈ G6.coreMod n from hm)
  · have hm1 : m = 1 := by
      have h := hm
      rw [show D.ker = ⊥ from rfl, Subgroup.mem_bot] at h
      exact h
    rw [hm1, show (D.act γ) 1 = 1 from map_one (G6.permAct n γ)]
    exact D.ker.one_mem
  · refine ⟨(QuotientGroup.mk' N).comp (Subgroup.subtype (⊤ : Subgroup ↥D.sec)), ?_, ?_, ?_⟩
    · intro x
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N x
      exact ⟨⟨m, Subgroup.mem_top m⟩, rfl⟩
    · intro u
      change QuotientGroup.mk (Subgroup.subtype (⊤ : Subgroup ↥D.sec) u) = 1 ↔
        (u : ↥D.sec) ∈ (⊥ : Subgroup ↥D.sec)
      rw [QuotientGroup.eq_one_iff, hN, Subgroup.mem_bot, Subgroup.mem_bot]
      rfl
    · intro γ u m hu hm hβu
      have h2 : (Subgroup.subtype (⊤ : Subgroup ↥D.sec) u) = m := by
        have h2 := (QuotientGroup.eq).1 hβu
        rw [hN, Subgroup.mem_bot, inv_mul_eq_one] at h2
        exact h2
      have h2' : (u : ↥D.sec) = m := h2
      refine congrArg QuotientGroup.mk (Subtype.ext ?_)
      show G6.permAct n γ ((u : ↥D.sec) : D.Amb) = G6.permAct n γ (m : D.Amb)
      rw [h2']

theorem s16c11_v1_symCore_of_altCore {n : ℕ} (hn : 7 ≤ n) {J : Type} [CommGroup J] [Finite J]
    {H H₀ : Subgroup (MulAut J)} (hHH₀ : H ≤ H₀) (hS : IsSym ↥H₀ n) (hA : UC22.IsAlt ↥H n)
    (hcomm : commV H = ⊤) (hR : (altCoreModel n).Realizes H ⊤ ⊥) :
    (G64.symCoreModel n).Realizes H₀ ⊤ ⊥ := by
  classical
  obtain ⟨π, hπ⟩ := hR
  have hπinj : Function.Injective π :=
    hπ.injective_of_faithful (s16c11_v1_altCore_faithful (by omega))
  let πe : ↥(alternatingGroup (Fin n)) ≃* ↥H :=
    MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv (D := altCoreModel n) rfl hπ
  let E' : J ≃* ↥(G6.coreMod n) := E
  have hEsub : ∀ (γ : ↥(alternatingGroup (Fin n))) (x : J),
      E' (((π γ : ↥H) : MulAut J) x) =
        G6.coreAct n (γ : Equiv.Perm (Fin n)) (E' x) := fun γ x => Subtype.ext (hE γ x)
  have hcoreE : ∀ γ : ↥(alternatingGroup (Fin n)),
      MulAut.congr E' (π γ) = G6.coreAct n (γ : Equiv.Perm (Fin n)) := by
    intro γ
    apply MulEquiv.ext
    intro w
    change E' (((π γ : ↥H) : MulAut J) (E'.symm w)) =
      (G6.coreAct n (γ : Equiv.Perm (Fin n))) w
    rw [hEsub γ (E'.symm w), MulEquiv.apply_symm_apply]
  have hcard : Nat.card ↥H₀ = 2 * Nat.card ↥H := s16c11_v1_card_two_mul (by omega) hS hA
  have hnorm : H₀ ≤ Subgroup.normalizer (H : Set (MulAut J)) :=
    s16c11_v1_normalizer_of_card_two_mul hHH₀ hcard
  have hconjH : ∀ g ∈ H₀, ∀ h ∈ H, g * h * g⁻¹ ∈ H := fun g hg h hh =>
    ((Subgroup.mem_normalizer_iff.mp (hnorm hg)) h).mp hh
  let K : Subgroup (MulAut ↥(G6.coreMod n)) := (G6.coreAct n).range
  have hπe_apply : ∀ γ : ↥(alternatingGroup (Fin n)), (πe γ : MulAut J) = π γ :=
    fun γ => rfl
  have hmemK : ∀ g ∈ H₀, MulAut.congr E' (g : MulAut J) ∈ K := by
    intro g hg
    let φ : MulAut ↥H :=
      { toFun := fun h => ⟨g * (h : MulAut J) * g⁻¹, hconjH g hg h h.2⟩
        invFun := fun h => ⟨g⁻¹ * (h : MulAut J) * g, by
          have := hconjH g⁻¹ (H₀.inv_mem hg) h h.2
          simpa using this⟩
        left_inv := fun h => Subtype.ext (by group)
        right_inv := fun h => Subtype.ext (by group)
        map_mul' := fun h h' => Subtype.ext (by simp [mul_assoc]) }
    have hφ_apply : ∀ h : ↥H, ((φ h : ↥H) : MulAut J) =
        g * (h : MulAut J) * g⁻¹ := fun h => rfl
    let ψ : MulAut ↥(alternatingGroup (Fin n)) := (MulAut.congr πe).symm φ
    have hψ : ∀ γ : ↥(alternatingGroup (Fin n)), φ (πe γ) = πe (ψ γ) := by
      intro γ
      have h1 : MulAut.congr πe ψ = φ := (MulAut.congr πe).apply_symm_apply φ
      have h2 := congrArg (fun e : MulAut ↥H => e (πe γ)) h1
      change πe (ψ (πe.symm (πe γ))) = φ (πe γ) at h2
      rw [MulEquiv.symm_apply_apply] at h2
      exact h2.symm
    obtain ⟨σ, hσ⟩ :=
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
        (by omega) (by omega)).2 ψ
    have hσperm : ∀ γ : ↥(alternatingGroup (Fin n)),
        (ψ γ : Equiv.Perm (Fin n)) =
          σ * (γ : Equiv.Perm (Fin n)) * σ⁻¹ := by
      intro γ
      have h := congrArg (fun x : ↥(alternatingGroup (Fin n)) => (x : Equiv.Perm (Fin n)))
        (congrArg (fun e : MulAut ↥(alternatingGroup (Fin n)) => e γ) hσ)
      simpa using h.symm
    let y : MulAut ↥(G6.coreMod n) := MulAut.congr E' (g : MulAut J)
    have hgconj : ∀ γ : ↥(alternatingGroup (Fin n)),
        g * (π γ : MulAut J) * g⁻¹ = (π (ψ γ) : MulAut J) := by
      intro γ
      have h := congrArg (fun x : ↥H => (x : MulAut J)) (hψ γ)
      rw [hφ_apply] at h
      simp only [hπe_apply] at h
      exact h
    have hyconj : ∀ γ : ↥(alternatingGroup (Fin n)),
        y * G6.coreAct n (γ : Equiv.Perm (Fin n)) * y⁻¹ =
          G6.coreAct n (ψ γ : Equiv.Perm (Fin n)) := by
      intro γ
      calc y * G6.coreAct n (γ : Equiv.Perm (Fin n)) * y⁻¹
          = y * MulAut.congr E' (π γ) * y⁻¹ := by rw [hcoreE γ]
        _ = MulAut.congr E' ((g : MulAut J) * (π γ) * (g : MulAut J)⁻¹) := by
              rw [map_mul, map_mul, map_inv]
        _ = MulAut.congr E' (π (ψ γ)) := by rw [hgconj γ]
        _ = G6.coreAct n (ψ γ : Equiv.Perm (Fin n)) := hcoreE (ψ γ)
    let z : MulAut ↥(G6.coreMod n) := y * (G6.coreAct n σ)⁻¹
    have hz : z = 1 := by
      have hmem : ∀ τ : ↥(alternatingGroup (Fin n)),
          σ⁻¹ * (τ : Equiv.Perm (Fin n)) * σ ∈ alternatingGroup (Fin n) := by
        intro τ
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_inv]
        have hτ : Equiv.Perm.sign (τ : Equiv.Perm (Fin n)) = 1 :=
          Equiv.Perm.mem_alternatingGroup.mp τ.2
        rw [hτ]
        simp
      have hψτ : ∀ τ : ↥(alternatingGroup (Fin n)),
          ψ ⟨σ⁻¹ * (τ : Equiv.Perm (Fin n)) * σ, hmem τ⟩ = τ := by
        intro τ
        apply Subtype.ext
        have h := hσperm ⟨σ⁻¹ * (τ : Equiv.Perm (Fin n)) * σ, hmem τ⟩
        rw [h]
        group
      refine s16c11_v1_coreAct_centralizer (n := n) (by omega) z fun τ x => ?_
      let τ' : ↥(alternatingGroup (Fin n)) :=
        ⟨σ⁻¹ * (τ : Equiv.Perm (Fin n)) * σ, hmem τ⟩
      have hcentral : z * G6.coreAct n (τ : Equiv.Perm (Fin n)) * z⁻¹ =
          G6.coreAct n (τ : Equiv.Perm (Fin n)) := by
        calc z * G6.coreAct n (τ : Equiv.Perm (Fin n)) * z⁻¹
            = y * G6.coreAct n (τ' : Equiv.Perm (Fin n)) * y⁻¹ := by
                rw [show z = y * (G6.coreAct n σ)⁻¹ from rfl, mul_inv_rev]
                rw [map_mul, map_mul, map_inv]
                group
          _ = G6.coreAct n (ψ τ' : Equiv.Perm (Fin n)) := hyconj τ'
          _ = G6.coreAct n (τ : Equiv.Perm (Fin n)) := by
                rw [show ψ τ' = τ from hψτ τ]
      have h2 : z * G6.coreAct n τ = G6.coreAct n τ * z := by
        have hh := congrArg (fun f => f * z) hcentral
        simpa [mul_assoc] using hh
      exact congrArg (fun f => f x) h2
    rw [show z = y * (G6.coreAct n σ)⁻¹ from rfl, mul_inv_eq_one] at hz
    exact ⟨σ, hz.symm⟩
  have hself := s16c11_v1_symCore_self n
  let j : ↥(⊤ : Subgroup J) ≃* ↥(G6.coreMod n) :=
    (Subgroup.topEquiv : (⊤ : Subgroup J) ≃* J).trans E'
  let rHom : ↥H₀ →* ↥K :=
    { toFun := fun g => ⟨MulAut.congr E' (g : MulAut J), hmemK g g.2⟩
      map_one' := Subtype.ext (map_one (MulAut.congr E'))
      map_mul' := fun g h =>
        Subtype.ext (map_mul (MulAut.congr E') (g : MulAut J) (h : MulAut J)) }
  have hcardH0 : Nat.card ↥H₀ = Nat.card (Equiv.Perm (Fin n)) := by
    obtain ⟨eS⟩ := hS
    rw [Nat.card_congr eS.toEquiv]
  have hcardK : Nat.card ↥K = Nat.card (Equiv.Perm (Fin n)) := by
    rw [← Nat.card_congr
      (MonoidHom.ofInjective (s16c11_v1_coreAct_injective (by omega))).toEquiv]
  have hinj : Function.Injective rHom := by
    intro g h hgh
    apply Subtype.ext
    have h1 : MulAut.congr E' (g : MulAut J) = MulAut.congr E' (h : MulAut J) :=
      congrArg Subtype.val hgh
    exact (MulAut.congr E').injective h1
  have hbij : Function.Bijective rHom :=
    hinj.bijective_of_nat_card_le (by rw [hcardH0, hcardK])
  let r : ↥H₀ ≃* ↥K := MulEquiv.ofBijective rHom hbij
  refine @CFSG.Quasithin.H.FFModel.realizes_of_equiv J (↥(G6.coreMod n))
    (inferInstance : CommGroup J) (Subgroup.toCommGroup (G6.coreMod n))
    (G64.symCoreModel n) H₀ ⊤ K
    (fun _ _ _ _ => Subgroup.mem_top _) j r ?_ hself
  intro h u
  change (E'.symm.trans ((h : MulAut J).trans E')) (E' (u : J)) =
    E' ((h : MulAut J) (u : J))
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
