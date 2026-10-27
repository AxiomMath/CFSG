module

public import CFSG.RankThree.PartTwo.Sec21.FF84S36TiA
public import CFSG.RankThree.PartTwo.Sec21.FF84S36TiHyp
public import CFSG.RankThree.PartTwo.Sec21.FF84S3M0

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

variable {G : Type} [Group G] [Finite G]

theorem R_exists_Q32 (hA9 : A9CentralizerStmt) {b t b₁ b₂ : G} {L B : Subgroup G}
    (d : F6Data b L B b₁ b₂ t) (h31 : FF84_3_1) :
    ∃ Q : Subgroup G, Q ≤ Cen t ⊓ Cen b₁ ∧ Nat.card Q = 32 := by
  have hZ : Subgroup.center L = ⊥ := (h31 G b L B b₁ b₂ d.sec).2
  obtain ⟨e, he⟩ := M0_model d.sec hZ
  have hb1L : b₁ ∈ L := (Subgroup.mem_inf.1 d.sec.hb₁).2
  have hb2L : b₂ ∈ L := (Subgroup.mem_inf.1 d.sec.hb₂).2
  have htc' : ∀ x ∈ L, t * x = x * t := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 d.htL x hx).symm
  obtain ⟨n, -, hnb, hnk, hnj⟩ := d.sec.mono.2.2.2.2.1
  have htt : t * t = 1 := by rw [← sq]; exact S36_sq_of_orderOf_two d.ht
  obtain ⟨hsq', hcb, hcb₁, hcb₂⟩ :=
    S36_monomial_conj htt d.htb (htc' b₁ hb1L) (htc' b₂ hb2L) hnb hnk hnj
  have ht'b : n * t * n⁻¹ ∈ Cen b := by
    apply S36_mem_cen_of
    have := mul_inv_eq_iff_eq_mul.1 hcb
    exact this.symm
  have ht'L : n * t * n⁻¹ ∈ L := S36_invol_cen_mem_L d h31 ht'b hsq'
  let τ : ↥L := ⟨n * t * n⁻¹, ht'L⟩
  let x₁ : ↥L := ⟨b₁, hb1L⟩
  let x₂ : ↥L := ⟨b₂, hb2L⟩
  obtain ⟨hm1, hm2⟩ := he x₁ x₂ rfl rfl
  have hττ : τ * τ = 1 := Subtype.ext hsq'
  have hτx₁ : τ * x₁ * τ⁻¹ = x₁⁻¹ := Subtype.ext hcb₁
  have hτx₂ : τ * x₂ * τ⁻¹ = x₂ := Subtype.ext hcb₂
  have hs_mem : ((e τ : alternatingGroup (Fin 8)) : P8) ∈ A8s := (e τ).2
  have hss : ((e τ : alternatingGroup (Fin 8)) : P8) * ((e τ : alternatingGroup (Fin 8)) : P8) = 1 := by
    have := congrArg (fun z => ((e z : alternatingGroup (Fin 8)) : P8)) hττ
    simpa using this
  have hsm1 : ((e τ : alternatingGroup (Fin 8)) : P8) * m₁ * ((e τ : alternatingGroup (Fin 8)) : P8)⁻¹
      = m₁⁻¹ := by
    have := congrArg (fun z => ((e z : alternatingGroup (Fin 8)) : P8)) hτx₁
    simpa [hm1] using this
  have hsm2 : ((e τ : alternatingGroup (Fin 8)) : P8) * m₂ * ((e τ : alternatingGroup (Fin 8)) : P8)⁻¹
      = m₂ := by
    have := congrArg (fun z => ((e z : alternatingGroup (Fin 8)) : P8)) hτx₂
    simpa [hm2] using this
  unfold A9CentralizerStmt at hA9
  obtain ⟨-, Q', hQ'A, hQ'C, -, -, hQ'card, -⟩ := hA9 _ hs_mem hss hsm1 hsm2
  let Q'' : Subgroup (alternatingGroup (Fin 8)) := Q'.subgroupOf (alternatingGroup (Fin 8))
  have hQ''card : Nat.card Q'' = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Q' ≤ alternatingGroup (Fin 8) from
      hQ'A)).toEquiv, hQ'card]
  let Q₁ : Subgroup ↥L := Q''.map e.symm.toMonoidHom
  let Q₂ : Subgroup G := Q₁.map L.subtype
  let Q₃ : Subgroup G := Q₂.map (MulAut.conj n⁻¹).toMonoidHom
  refine ⟨Q₃, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨l, hl, rfl⟩ := hq
    obtain ⟨a, ha, hal⟩ := hl
    have haQ : (a : P8) ∈ Q' := ha
    have hcs : ((e τ : alternatingGroup (Fin 8)) : P8) * (a : P8) =
        (a : P8) * ((e τ : alternatingGroup (Fin 8)) : P8) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hQ'C haQ) |>.symm
    have hel : e l = a := by rw [← hal]; simp
    have hτl : τ * l = l * τ := by
      apply e.injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hel]
      exact hcs
    have hq1 : (n * t * n⁻¹) * (l : G) = (l : G) * (n * t * n⁻¹) := congrArg Subtype.val hτl
    have hq2 : b * (l : G) = (l : G) * b :=
      (S36_comm_of_cen (d.sec.hyp.hLC l.2))
    refine Subgroup.mem_inf.2 ⟨S36_mem_cen_of ?_, S36_mem_cen_of ?_⟩
    · show t * (n⁻¹ * (l : G) * n⁻¹⁻¹) = (n⁻¹ * (l : G) * n⁻¹⁻¹) * t
      calc t * (n⁻¹ * (l : G) * n⁻¹⁻¹) = n⁻¹ * ((n * t * n⁻¹) * (l : G)) * n := by group
        _ = n⁻¹ * ((l : G) * (n * t * n⁻¹)) * n := by rw [hq1]
        _ = (n⁻¹ * (l : G) * n⁻¹⁻¹) * t := by group
    · show b₁ * (n⁻¹ * (l : G) * n⁻¹⁻¹) = (n⁻¹ * (l : G) * n⁻¹⁻¹) * b₁
      have hb1 : b₁ = n⁻¹ * b * n := by rw [← hnk]; group
      calc b₁ * (n⁻¹ * (l : G) * n⁻¹⁻¹) = n⁻¹ * (b * (l : G)) * n := by rw [hb1]; group
        _ = n⁻¹ * ((l : G) * b) * n := by rw [hq2]
        _ = (n⁻¹ * (l : G) * n⁻¹⁻¹) * b₁ := by rw [hb1]; group
  · rw [Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective,
      Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hQ''card]

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
