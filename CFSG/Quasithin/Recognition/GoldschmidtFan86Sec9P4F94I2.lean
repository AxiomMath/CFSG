module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94Cnt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94Iso

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem dist_alpha_beta : Γ.dist S.α S.beta = 1 := dist_eq_one_iff_adj.2 (S.D.adj_start_beta 2)

theorem dist_beta_alpha_le (F : FanTree Γ G) (j : Fin 5) : Γ.dist S.beta (S.D.alpha j) ≤ 3 := by
  calc Γ.dist S.beta (S.D.alpha j) ≤ Γ.dist S.beta S.α + Γ.dist S.α (S.D.alpha j) :=
        F.isTree.connected.dist_triangle
    _ = 1 + 2 := by
        rw [SimpleGraph.dist_comm, S.dist_alpha_beta, S.D.dist_start_alpha F j]
    _ = 3 := rfl

theorem commute_zNb_label (F : FanTree Γ G) (h71c : Fan71c F L) (i : Fin 3) {l : V}
    (hl : valence Γ l = 5) (hd : Γ.dist S.beta l ≤ 3) : Commute (S.zNb i) (L.z l) := by
  have hdd : Γ.dist (S.alphaV i) l ≤ 4 := by
    calc Γ.dist (S.alphaV i) l ≤ Γ.dist (S.alphaV i) S.beta + Γ.dist S.beta l :=
          F.isTree.connected.dist_triangle
      _ ≤ 1 + 3 := by
          gcongr
          rw [SimpleGraph.dist_comm]
          exact (S.dist_beta_alphaV F i).le
      _ = 4 := rfl
  exact h71c.z_comm_of_dist_le (a := S.alphaV i) (b := l) (S.valence_alphaV F i) hl hdd

theorem commute_zNb_ub (F : FanTree Γ G) (h71c : Fan71c F L) (i : Fin 3) :
    Commute (S.zNb i) S.ub := by
  rw [S.ub_eq]
  have h1 := S.commute_zNb_label F h71c i (S.D.valence_alpha F 1) (S.dist_beta_alpha_le F 1)
  have h3 := S.commute_zNb_label F h71c i (S.D.valence_alpha F 3) (S.dist_beta_alpha_le F 3)
  have h0 := S.commute_zNb_label F h71c i S.D.val
    (by rw [SimpleGraph.dist_comm, S.dist_alpha_beta]; norm_num)
  exact (h1.mul_right h3).mul_right h0

theorem ub_mul_self (F : FanTree Γ G) (h71c : Fan71c F L) : S.ub * S.ub = 1 := by
  rw [S.ub_eq]
  have c13 : S.zMu1 1 * S.zMu1 3 = S.zMu1 3 * S.zMu1 1 := (S.zMu1_commute F h71c 1 3).eq
  have c10 : S.zMu1 1 * L.z S.α = L.z S.α * S.zMu1 1 := (S.zMu1_comm_alpha F h71c 1).eq
  have c30 : S.zMu1 3 * L.z S.α = L.z S.α * S.zMu1 3 := (S.zMu1_comm_alpha F h71c 3).eq
  have s1 := S.zMu1_mul_self F 1
  have s3 := S.zMu1_mul_self F 3
  have s0 : L.z S.α * L.z S.α = 1 := L.z_mul_self S.D.val
  calc S.zMu1 1 * S.zMu1 3 * L.z S.α * (S.zMu1 1 * S.zMu1 3 * L.z S.α)
      = S.zMu1 1 * (S.zMu1 3 * (L.z S.α * S.zMu1 1)) * S.zMu1 3 * L.z S.α := by group
    _ = S.zMu1 1 * (S.zMu1 3 * (S.zMu1 1 * L.z S.α)) * S.zMu1 3 * L.z S.α := by rw [c10]
    _ = S.zMu1 1 * ((S.zMu1 3 * S.zMu1 1) * L.z S.α) * S.zMu1 3 * L.z S.α := by group
    _ = S.zMu1 1 * ((S.zMu1 1 * S.zMu1 3) * L.z S.α) * S.zMu1 3 * L.z S.α := by rw [← c13]
    _ = (S.zMu1 1 * S.zMu1 1) * S.zMu1 3 * (L.z S.α * S.zMu1 3) * L.z S.α := by group
    _ = (S.zMu1 1 * S.zMu1 1) * S.zMu1 3 * (S.zMu1 3 * L.z S.α) * L.z S.α := by rw [← c30]
    _ = (S.zMu1 1 * S.zMu1 1) * (S.zMu1 3 * S.zMu1 3) * (L.z S.α * L.z S.α) := by group
    _ = 1 := by rw [s1, s3, s0]; group

theorem exists_bottom_iso (F : FanTree Γ G) (h7 : Fan7 F L) (h65 : Fan65 F) (h81 : Fan81 F L)
    (h82 : Fan82 F L) (h83b : Fan83b F L) (h512 : Fan512 F L)
    (hw : S.w ∈ nbrStab Γ G S.beta) (hwA : S.wA 1 ∈ nbrStab Γ G S.beta)
    (hc : S.c ∈ nbrStab Γ G S.beta)
    (htop : 8 * Nat.card S.D.calpha ≤ (ballStab Γ G 2 S.beta).relIndex
      (Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta)) :
    ∃ φ : ↥(ballStab Γ G 3 S.beta) →* (Fin 3 → Multiplicative (ZMod 2)),
      Function.Surjective φ ∧
        φ.ker = (ballStab Γ G 4 S.beta).subgroupOf (ballStab Γ G 3 S.beta) := by
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨-, -, h8⟩ := S.fan94_exact_of F h7 h65 h81 h82 h83b h512 hw hwA hc htop
  obtain ⟨-, -, e3⟩ := S.fan94b_of F h7 h65 h81 h82 h83b h512 hw hwA hc htop
  rw [e3] at h8 ⊢
  rw [S.ballStab_four_beta h7, Subgroup.bot_subgroupOf]
  set k : Set G := insert S.ub (Set.range S.zNb) with hk
  have hcommk : k.Pairwise Commute := by
    intro x hx y hy hxy
    rcases hx with rfl | ⟨i, rfl⟩ <;> rcases hy with rfl | ⟨j, rfl⟩
    · exact absurd rfl hxy
    · exact (S.commute_zNb_ub F h71c j).symm
    · exact S.commute_zNb_ub F h71c i
    · exact S.f94_zNb_commute F h71c i j
  have : IsMulCommutative ↥(Subgroup.closure k) := Subgroup.isMulCommutative_closure hcommk
  let _ : CommGroup ↥(Subgroup.closure k) :=
    { (inferInstance : Group ↥(Subgroup.closure k)) with
      mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  let a : ↥(Subgroup.closure k) := ⟨S.zNb 0, Subgroup.subset_closure (Or.inr ⟨0, rfl⟩)⟩
  let b : ↥(Subgroup.closure k) := ⟨S.zNb 1, Subgroup.subset_closure (Or.inr ⟨1, rfl⟩)⟩
  let u : ↥(Subgroup.closure k) := ⟨S.ub, Subgroup.subset_closure (Or.inl rfl)⟩
  have ha2 : a ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using S.f94_zNb_mul_self F 0)
  have hb2 : b ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using S.f94_zNb_mul_self F 1)
  have hu2 : u ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using S.ub_mul_self F h71c)
  let ι : (Fin 3 → Multiplicative (ZMod 2)) →* ↥(Subgroup.closure k) :=
    ((zmodHom a 2 ha2).comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod 2)) 0)) *
    ((zmodHom b 2 hb2).comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod 2)) 1)) *
    ((zmodHom u 2 hu2).comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod 2)) 2))
  have h1val : ZMod.val (1 : ZMod 2) = 1 := rfl
  have hιa : ι (fun j => if j = 0 then Multiplicative.ofAdd 1 else 1) = a := by
    simp [ι, zmodHom_apply, h1val]
  have hιb : ι (fun j => if j = 1 then Multiplicative.ofAdd 1 else 1) = b := by
    simp [ι, zmodHom_apply, h1val]
  have hιu : ι (fun j => if j = 2 then Multiplicative.ofAdd 1 else 1) = u := by
    simp [ι, zmodHom_apply, h1val]
  have hab : S.zNb 0 * S.zNb 1 = S.zNb 2 := by
    have hprod : S.zNb 0 * S.zNb 1 * S.zNb 2 = 1 := by
      rw [S.zNb_zero]
      exact S.zNb_prod F h512
    rw [eq_inv_of_mul_eq_one_left hprod]
    exact inv_eq_of_mul_eq_one_right (S.f94_zNb_mul_self F 2)
  have hsurj : Function.Surjective ι := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := k)]
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    rcases hx with hx | ⟨i, hi⟩
    · have : x = u := Subtype.ext hx
      rw [this, ← hιu]
      exact ⟨_, rfl⟩
    · have hx' : x = ⟨S.zNb i, Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)⟩ := Subtype.ext hi.symm
      rw [hx']
      fin_cases i
      · show a ∈ ι.range
        rw [← hιa]
        exact ⟨_, rfl⟩
      · show b ∈ ι.range
        rw [← hιb]
        exact ⟨_, rfl⟩
      · have hab' : (⟨S.zNb 2, Subgroup.subset_closure (Or.inr ⟨2, rfl⟩)⟩ :
            ↥(Subgroup.closure k)) = a * b := Subtype.ext hab.symm
        show (⟨S.zNb 2, _⟩ : ↥(Subgroup.closure k)) ∈ ι.range
        rw [hab', ← hιa, ← hιb, ← map_mul]
        exact ⟨_, rfl⟩
  have hcardPi : Nat.card (Fin 3 → Multiplicative (ZMod 2)) = 8 := by
    rw [Nat.card_pi]
    simp
  have hbij : Function.Bijective ι :=
    hsurj.bijective_of_nat_card_le (by rw [hcardPi, h8])
  let e := MulEquiv.ofBijective ι hbij
  refine ⟨e.symm.toMonoidHom, e.symm.surjective, ?_⟩
  exact (MonoidHom.ker_eq_bot_iff _).2 e.symm.injective

end Sec9Cfg

end CFSG.Quasithin.Fan86
