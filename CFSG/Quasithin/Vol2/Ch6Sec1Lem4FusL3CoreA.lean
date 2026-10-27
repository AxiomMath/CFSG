module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxDefs
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxLift

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.RankThree.SubgroupLists

section CoreA

variable {F : Type} [Field F] [Finite F] {S : Subgroup (GL (Fin 3) F)}
  {Bl : Subgroup (GL (Fin 2) F)} {p : ℕ} {G : Type*} [Group G] {ψ : ↥S →* G}

private theorem blk_entry22_L3core (X : GL (Fin 2) F) :
    ((blk X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 =
      ((X : Matrix (Fin 2) (Fin 2) F).det)⁻¹ := by
  rw [coe_blk]
  simp [blkMat]

private theorem negDiag3_mul_self_L3core :
    negDiag3 F * negDiag3 F = (1 : GL (Fin 3) F) := by
  apply Units.ext
  rw [Units.val_mul, coe_negDiag3, Units.val_one, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> norm_num

private theorem eq_one_of_conj_scalar_L3core {X : GL (Fin 2) F}
    (hX : Matrix.GeneralLinearGroup.det X = 1) (q : GL (Fin 3) F) {c : Fˣ}
    (h : q * blk X * q⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) c) : X = 1 := by
  have hbX : blk X = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    have e : blk X = q⁻¹ * (q * blk X * q⁻¹) * q := by group
    rw [e, h, mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc,
      inv_mul_cancel, one_mul]
  have hXm : (X : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hX, Units.val_one]
  have h22 := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) 2 2) hbX
  simp only [blk_entry22_L3core, hXm, inv_one, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h22
  have hc : c = 1 := Units.ext (by simpa using h22.symm)
  apply blk_injective
  rw [hbX, hc, map_one, map_one]

private theorem ker_central_L3core (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) :
    ψ.ker ≤ Subgroup.center S :=
  fun z hz => CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center S (hker hz)

private theorem ker_cube_L3core (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) : ∀ z ∈ ψ.ker, z ^ 3 = 1 := by
  intro z hz
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp (hker hz))
  have hdet : Matrix.GeneralLinearGroup.det (z : GL (Fin 3) F) = 1 := by
    apply Units.ext
    rw [Units.val_one, Matrix.GeneralLinearGroup.val_det_apply]
    exact hS.det_one _ z.2
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  apply Subtype.ext
  show (z : GL (Fin 3) F) ^ 3 = 1
  rw [← hc, ← map_pow, hdet, map_one]

private theorem sq_one_of_orderOf_two_L3core {H : Type*} [Group H] {x : H}
    (hx : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← hx, pow_orderOf_eq_one]

private theorem coe_ne_one_of_orderOf_L3core {x : ↥S} (hx : orderOf (ψ x) = 2) :
    (x : GL (Fin 3) F) ≠ 1 := by
  intro h
  have h1 : x = 1 := Subtype.ext h
  rw [h1, map_one, orderOf_one] at hx
  norm_num at hx

private theorem coe_sq_one_L3core {x : ↥S} (hx : x * x = 1) :
    (x : GL (Fin 3) F) * x = 1 := by
  have := congrArg Subtype.val hx
  simpa using this

private theorem det_sl2_L3core {b : GL (Fin 2) F} (hb : b ∈ sl2Of Bl) :
    Matrix.GeneralLinearGroup.det b = 1 :=
  MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hb).2

private theorem mem_of_sl2_L3core {b : GL (Fin 2) F} (hb : b ∈ sl2Of Bl) : b ∈ Bl :=
  (Subgroup.mem_inf.mp hb).1

private theorem mem_sl2_of_L3core {b : GL (Fin 2) F} (hb : b ∈ Bl)
    (hd : Matrix.GeneralLinearGroup.det b = 1) : b ∈ sl2Of Bl :=
  Subgroup.mem_inf.mpr ⟨hb, MonoidHom.mem_ker.mpr hd⟩

private theorem exists_b0_L3core (hS : L3Shape F S Bl p) :
    ∃ b₀ : GL (Fin 2) F, b₀ ∈ sl2Of Bl ∧ blk b₀ = negDiag3 F := by
  obtain ⟨b₀, hb₀Bl, hb₀⟩ := (hS.cent _ hS.neg_mem).mp rfl
  refine ⟨b₀, mem_sl2_of_L3core hb₀Bl ?_, hb₀⟩
  have h1 : (b₀ : Matrix (Fin 2) (Fin 2) F) =
      ulBlock ((negDiag3 F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← hb₀, ulBlock_blk]
  apply Units.ext
  rw [Units.val_one, Matrix.GeneralLinearGroup.val_det_apply, h1, coe_negDiag3]
  simp [ulBlock, Matrix.det_fin_two]

private noncomputable def conjBlk_L3core (q : GL (Fin 3) F) : GL (Fin 2) F →* GL (Fin 3) F :=
  (MulAut.conj q).toMonoidHom.comp blk

private theorem conjBlk_apply_L3core (q : GL (Fin 3) F) (B : GL (Fin 2) F) :
    conjBlk_L3core q B = q * blk B * q⁻¹ := rfl

private theorem conjBlk_mem_L3core (hS : L3Shape F S Bl p) {q : ↥S} {B : GL (Fin 2) F}
    (hB : B ∈ Bl) : (q : GL (Fin 3) F) * blk B * (q : GL (Fin 3) F)⁻¹ ∈ S :=
  S.mul_mem (S.mul_mem q.2 (hS.blk_mem B hB)) (S.inv_mem q.2)

private noncomputable def phiConj_L3core (hS : L3Shape F S Bl p) (q : ↥S) :
    ↥(sl2Of Bl) →* ↥S :=
  ((conjBlk_L3core (q : GL (Fin 3) F)).comp (sl2Of Bl).subtype).codRestrict S
    (fun b => conjBlk_mem_L3core (q := q) hS (B := (b : GL (Fin 2) F)) (mem_of_sl2_L3core b.2))

private abbrev invL3core (hS : L3Shape F S Bl p) (q : ↥S) : ↥S :=
  q * ⟨negDiag3 F, hS.neg_mem⟩ * q⁻¹

private theorem invL3core_sq (hS : L3Shape F S Bl p) (q : ↥S) :
    invL3core hS q * invL3core hS q = 1 := by
  have hn : (⟨negDiag3 F, hS.neg_mem⟩ : ↥S) * ⟨negDiag3 F, hS.neg_mem⟩ = 1 :=
    Subtype.ext negDiag3_mul_self_L3core
  unfold invL3core
  calc q * ⟨negDiag3 F, hS.neg_mem⟩ * q⁻¹ * (q * ⟨negDiag3 F, hS.neg_mem⟩ * q⁻¹)
      = q * (⟨negDiag3 F, hS.neg_mem⟩ * ⟨negDiag3 F, hS.neg_mem⟩) * q⁻¹ := by group
    _ = 1 := by rw [hn]; group

private theorem cent_iff_L3core (hS : L3Shape F S Bl p) (q : ↥S) {x : GL (Fin 3) F}
    (hx : x ∈ S) :
    x * ((q : GL (Fin 3) F) * negDiag3 F * (q : GL (Fin 3) F)⁻¹) =
        ((q : GL (Fin 3) F) * negDiag3 F * (q : GL (Fin 3) F)⁻¹) * x ↔
      ∃ B ∈ Bl, conjBlk_L3core (q : GL (Fin 3) F) B = x := by
  constructor
  · intro h
    have hy : (q : GL (Fin 3) F)⁻¹ * x * (q : GL (Fin 3) F) ∈ S :=
      S.mul_mem (S.mul_mem (S.inv_mem q.2) hx) q.2
    have hc : ((q : GL (Fin 3) F)⁻¹ * x * (q : GL (Fin 3) F)) * negDiag3 F =
        negDiag3 F * ((q : GL (Fin 3) F)⁻¹ * x * (q : GL (Fin 3) F)) := by
      calc ((q : GL (Fin 3) F)⁻¹ * x * (q : GL (Fin 3) F)) * negDiag3 F
          = (q : GL (Fin 3) F)⁻¹ * (x * ((q : GL (Fin 3) F) * negDiag3 F * (q : GL (Fin 3) F)⁻¹))
              * (q : GL (Fin 3) F) := by group
        _ = (q : GL (Fin 3) F)⁻¹ * (((q : GL (Fin 3) F) * negDiag3 F * (q : GL (Fin 3) F)⁻¹) * x)
              * (q : GL (Fin 3) F) := by rw [h]
        _ = negDiag3 F * ((q : GL (Fin 3) F)⁻¹ * x * (q : GL (Fin 3) F)) := by group
    obtain ⟨B, hB, hBy⟩ := (hS.cent _ hy).mp hc
    refine ⟨B, hB, ?_⟩
    rw [conjBlk_apply_L3core, hBy]
    group
  · rintro ⟨B, hB, rfl⟩
    rw [conjBlk_apply_L3core]
    calc (q : GL (Fin 3) F) * blk B * (q : GL (Fin 3) F)⁻¹ *
          ((q : GL (Fin 3) F) * negDiag3 F * (q : GL (Fin 3) F)⁻¹)
        = (q : GL (Fin 3) F) * (blk B * negDiag3 F) * (q : GL (Fin 3) F)⁻¹ := by group
      _ = (q : GL (Fin 3) F) * (negDiag3 F * blk B) * (q : GL (Fin 3) F)⁻¹ := by
          rw [blk_commute_negDiag3]
      _ = ((q : GL (Fin 3) F) * negDiag3 F * (q : GL (Fin 3) F)⁻¹) *
          ((q : GL (Fin 3) F) * blk B * (q : GL (Fin 3) F)⁻¹) := by group

private theorem centralizer_map_L3core (hS : L3Shape F S Bl p) (q : ↥S) :
    Subgroup.map (Subgroup.subtype S) (Subgroup.centralizer ({invL3core hS q} : Set ↥S)) =
      Subgroup.map (conjBlk_L3core (q : GL (Fin 3) F)) Bl := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : GL (Fin 3) F) * ((q : GL (Fin 3) F) * negDiag3 F * (q : GL (Fin 3) F)⁻¹) =
        ((q : GL (Fin 3) F) * negDiag3 F * (q : GL (Fin 3) F)⁻¹) * (y : GL (Fin 3) F) :=
      congrArg Subtype.val hy
    obtain ⟨B, hB, hBy⟩ := (cent_iff_L3core hS q y.2).mp hy'
    exact ⟨B, hB, hBy⟩
  · rintro ⟨B, hB, rfl⟩
    refine ⟨⟨conjBlk_L3core (q : GL (Fin 3) F) B, conjBlk_mem_L3core hS hB⟩, ?_, rfl⟩
    apply Subtype.ext
    exact (cent_iff_L3core hS q (conjBlk_mem_L3core hS hB)).mpr ⟨B, hB, rfl⟩

private theorem sl2_map_L3core (hS : L3Shape F S Bl p) (q : ↥S) :
    Subgroup.map (Subgroup.subtype S) (phiConj_L3core hS q).range =
      Subgroup.map (conjBlk_L3core (q : GL (Fin 3) F)) (sl2Of Bl) := by
  ext x
  simp only [Subgroup.mem_map, MonoidHom.mem_range, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, b.2, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨phiConj_L3core hS q ⟨B, hB⟩, ⟨⟨B, hB⟩, rfl⟩, rfl⟩

private theorem derived_cent_L3core (hS : L3Shape F S Bl p) (q : ↥S) :
    ⁅Subgroup.centralizer ({invL3core hS q} : Set ↥S),
      Subgroup.centralizer ({invL3core hS q} : Set ↥S)⁆ = (phiConj_L3core hS q).range := by
  refine Subgroup.map_injective (f := Subgroup.subtype S) (Subgroup.subtype_injective S) ?_
  rw [Subgroup.map_commutator, centralizer_map_L3core hS q, ← Subgroup.map_commutator,
    hS.derived_eq, sl2_map_L3core hS q]

private theorem leviOfL3_eq_L3core (hS : L3Shape F S Bl p)
    (hcen : ψ.ker ≤ Subgroup.center S) (h3 : ∀ z ∈ ψ.ker, z ^ 3 = 1) (q : ↥S) :
    leviOfL3 ψ.range (ψ (invL3core hS q)) = (ψ.comp (phiConj_L3core hS q)).range := by
  rw [leviOfL3_range_eq hcen h3 (invL3core_sq hS q), derived_cent_L3core hS q,
    MonoidHom.range_comp]

private theorem mem_center_equiv_L3core {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    e a ∈ Subgroup.center B ↔ a ∈ Subgroup.center A := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e g)
  · intro h y
    obtain ⟨g, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, h g]

private theorem central_block_L3core (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) (q : ↥S) {c : ↥S}
    {B : GL (Fin 2) F} (hB : B ∈ Bl)
    (hBc : conjBlk_L3core (q : GL (Fin 3) F) B = (c : GL (Fin 3) F))
    (hcK : ∀ k ∈ (ψ.comp (phiConj_L3core hS q)).range, k * ψ c = ψ c * k) :
    ∀ A : GL (Fin 2) F, B * A = A * B := by
  have hBcomm : ∀ b ∈ sl2Of Bl, B * b = b * B := by
    intro b hb
    have hxc0 := hcK (ψ (phiConj_L3core hS q ⟨b, hb⟩))
      (MonoidHom.mem_range.mpr ⟨⟨b, hb⟩, rfl⟩)
    generalize hx : phiConj_L3core hS q ⟨b, hb⟩ = x at hxc0
    have hxq : (x : GL (Fin 3) F) = (q : GL (Fin 3) F) * blk b * (q : GL (Fin 3) F)⁻¹ := by
      subst hx
      rfl
    have hz : x * c * x⁻¹ * c⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hxc0]
      group
    obtain ⟨c₀, hc₀⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp (hker hz))
    have hcq : (c : GL (Fin 3) F) = (q : GL (Fin 3) F) * blk B * (q : GL (Fin 3) F)⁻¹ :=
      hBc.symm
    have hkey : (q : GL (Fin 3) F) * blk (b * B * b⁻¹ * B⁻¹) * (q : GL (Fin 3) F)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) c₀ := by
      rw [hc₀]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxq, hcq, map_mul, map_inv]
      group
    have hdet : Matrix.GeneralLinearGroup.det (b * B * b⁻¹ * B⁻¹) = 1 := by
      simp [map_mul, map_inv, det_sl2_L3core hb]
    have h1 := eq_one_of_conj_scalar_L3core hdet (q : GL (Fin 3) F) hkey
    have h2 : (b * B) * (B * b)⁻¹ = 1 := by
      rw [show (b * B) * (B * b)⁻¹ = b * B * b⁻¹ * B⁻¹ by group]
      exact h1
    exact (mul_inv_eq_one.mp h2).symm
  obtain ⟨l, hl⟩ := hS.scalar_of_commute B hB hBcomm
  intro A
  rw [hl]
  exact Matrix.GeneralLinearGroup.scalar_commute l A

private theorem centralizer_commute_L3core (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) (q c g : ↥S)
    (hcu : Commute (ψ c) (ψ (invL3core hS q))) (hgu : Commute (ψ g) (ψ (invL3core hS q)))
    (hcK : ∀ k ∈ (ψ.comp (phiConj_L3core hS q)).range, k * ψ c = ψ c * k) :
    Commute (ψ c) (ψ g) := by
  have hcomm : c * invL3core hS q = invL3core hS q * c :=
    commute_of_map_commute_L3 (ker_central_L3core hker) (ker_cube_L3core hS hker)
      (invL3core_sq hS q) hcu
  have hgcomm : g * invL3core hS q = invL3core hS q * g :=
    commute_of_map_commute_L3 (ker_central_L3core hker) (ker_cube_L3core hS hker)
      (invL3core_sq hS q) hgu
  have hcomm' : (c : GL (Fin 3) F) * ((q : GL (Fin 3) F) * negDiag3 F * (q : GL (Fin 3) F)⁻¹) =
      ((q : GL (Fin 3) F) * negDiag3 F * (q : GL (Fin 3) F)⁻¹) * (c : GL (Fin 3) F) :=
    congrArg Subtype.val hcomm
  have hgcomm' : (g : GL (Fin 3) F) * ((q : GL (Fin 3) F) * negDiag3 F * (q : GL (Fin 3) F)⁻¹) =
      ((q : GL (Fin 3) F) * negDiag3 F * (q : GL (Fin 3) F)⁻¹) * (g : GL (Fin 3) F) :=
    congrArg Subtype.val hgcomm
  obtain ⟨B, hB, hBc⟩ := (cent_iff_L3core hS q c.2).mp hcomm'
  obtain ⟨A, hA, hAg⟩ := (cent_iff_L3core hS q g.2).mp hgcomm'
  have hBcen := central_block_L3core hS hker q hB hBc hcK
  have key : c * g = g * c := by
    apply Subtype.ext
    show (c : GL (Fin 3) F) * g = g * c
    rw [← hBc, ← hAg, conjBlk_apply_L3core, conjBlk_apply_L3core]
    calc (q : GL (Fin 3) F) * blk B * (q : GL (Fin 3) F)⁻¹ *
          ((q : GL (Fin 3) F) * blk A * (q : GL (Fin 3) F)⁻¹)
        = (q : GL (Fin 3) F) * blk (B * A) * (q : GL (Fin 3) F)⁻¹ := by
          rw [map_mul]; group
      _ = (q : GL (Fin 3) F) * blk (A * B) * (q : GL (Fin 3) F)⁻¹ := by rw [hBcen A]
      _ = (q : GL (Fin 3) F) * blk A * (q : GL (Fin 3) F)⁻¹ *
          ((q : GL (Fin 3) F) * blk B * (q : GL (Fin 3) F)⁻¹) := by
          rw [map_mul]; group
  show ψ c * ψ g = ψ g * ψ c
  rw [← map_mul, ← map_mul, key]

private theorem isL3Levi_L3core (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) (q : ↥S)
    (hu2 : orderOf (ψ (invL3core hS q)) = 2) :
    IsL3Levi (ψ.comp (phiConj_L3core hS q)).range (ψ (invL3core hS q)) p := by
  obtain ⟨b₀, hb₀, hb₀blk⟩ := exists_b0_L3core hS
  have hinj : Function.Injective (ψ.comp (phiConj_L3core hS q)) := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hφb : phiConj_L3core hS q b ∈ ψ.ker := hb
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp (hker hφb))
    apply Subtype.ext
    show (b : GL (Fin 2) F) = 1
    exact eq_one_of_conj_scalar_L3core (det_sl2_L3core b.2) (q : GL (Fin 3) F) hc.symm
  set ι := ψ.comp (phiConj_L3core hS q) with hι
  have hιb₀ : ι ⟨b₀, hb₀⟩ = ψ (invL3core hS q) := by
    show ψ (phiConj_L3core hS q ⟨b₀, hb₀⟩) = ψ (invL3core hS q)
    congr 1
    apply Subtype.ext
    show (q : GL (Fin 3) F) * blk b₀ * (q : GL (Fin 3) F)⁻¹ =
      (q : GL (Fin 3) F) * negDiag3 F * (q : GL (Fin 3) F)⁻¹
    rw [hb₀blk]
  obtain ⟨e, he⟩ : ∃ e : ↥(sl2Of Bl) ≃* ↥(ι.range), ∀ b, ((e b : ↥(ι.range)) : G) = ι b :=
    ⟨MonoidHom.ofInjective hinj, fun b => rfl⟩
  have hu_mem : ψ (invL3core hS q) ∈ ι.range := MonoidHom.mem_range.mpr ⟨⟨b₀, hb₀⟩, hιb₀⟩
  have hcenter : ∀ x : ↥(ι.range), x ∈ Subgroup.center ↥(ι.range) ↔
      ((x : G) = 1 ∨ (x : G) = ψ (invL3core hS q)) := by
    intro x
    obtain ⟨b, rfl⟩ := e.surjective x
    have h1 : blk (b : GL (Fin 2) F) = 1 ↔ b = 1 := by
      rw [← map_one blk, blk_injective.eq_iff]
      exact ⟨fun h => Subtype.ext h, fun h => by subst h; rfl⟩
    have h2 : blk (b : GL (Fin 2) F) = negDiag3 F ↔ b = ⟨b₀, hb₀⟩ := by
      rw [← hb₀blk, blk_injective.eq_iff]
      exact ⟨fun h => Subtype.ext h, fun h => by subst h; rfl⟩
    have h3 : ι b = 1 ↔ b = 1 := by
      rw [← map_one ι, hinj.eq_iff]
    have h4 : ι b = ψ (invL3core hS q) ↔ b = ⟨b₀, hb₀⟩ := by
      rw [← hιb₀, hinj.eq_iff]
    rw [mem_center_equiv_L3core e b, he b, hS.sl2_center b, h1, h2, h3, h4]
  unfold IsL3Levi
  obtain ⟨F₀, hF₀, hF₀fin, hcard, ⟨eq⟩⟩ := hS.sl2_psl
  haveI := hS.sl2_perfect
  refine ⟨hu2, hu_mem, hcenter, ?_, F₀, hF₀, hF₀fin, hcard,
    ⟨(QuotientGroup.congr (Subgroup.center ↥(ι.range)) (Subgroup.center ↥(sl2Of Bl)) e.symm
      (Subgroup.map_center_eq e.symm)).trans eq⟩⟩
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem L3Shape.invConj (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) :
    ∀ u ∈ ψ.range, ∀ v ∈ ψ.range, orderOf u = 2 → orderOf v = 2 →
      ∃ g ∈ ψ.range, g * u * g⁻¹ = v := by
  intro u hu v hv hu2 hv2
  obtain ⟨a, ha, rfl⟩ :=
    lift_involution_L3 (ker_cube_L3core hS hker) hu (sq_one_of_orderOf_two_L3core hu2)
  obtain ⟨b, hb, rfl⟩ :=
    lift_involution_L3 (ker_cube_L3core hS hker) hv (sq_one_of_orderOf_two_L3core hv2)
  obtain ⟨g₁, hg₁, h₁⟩ := hS.conj (a : GL (Fin 3) F) a.2 (coe_sq_one_L3core ha)
    (coe_ne_one_of_orderOf_L3core hu2)
  obtain ⟨g₂, hg₂, h₂⟩ := hS.conj (b : GL (Fin 3) F) b.2 (coe_sq_one_L3core hb)
    (coe_ne_one_of_orderOf_L3core hv2)
  have hh : g₂ * g₁⁻¹ ∈ S := S.mul_mem hg₂ (S.inv_mem hg₁)
  have ea : (a : GL (Fin 3) F) = g₁ * negDiag3 F * g₁⁻¹ := by
    rw [← h₁]; group
  have eb : (b : GL (Fin 3) F) = g₂ * negDiag3 F * g₂⁻¹ := by
    rw [← h₂]; group
  have key : (⟨g₂ * g₁⁻¹, hh⟩ : ↥S) * a * (⟨g₂ * g₁⁻¹, hh⟩ : ↥S)⁻¹ = b := by
    apply Subtype.ext
    show (g₂ * g₁⁻¹) * (a : GL (Fin 3) F) * (g₂ * g₁⁻¹)⁻¹ = (b : GL (Fin 3) F)
    rw [ea, eb]
    group
  refine ⟨ψ ⟨g₂ * g₁⁻¹, hh⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, key]

theorem L3Shape.levi (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) :
    ∀ u ∈ ψ.range, orderOf u = 2 →
      IsL3Levi (leviOfL3 ψ.range u) u p ∧
        ∀ c ∈ ψ.range, Commute c u → c ∈ Subgroup.centralizer (leviOfL3 ψ.range u : Set G) →
          ∀ g ∈ ψ.range, Commute g u → Commute c g := by
  intro u hu hu2
  obtain ⟨a, ha, rfl⟩ :=
    lift_involution_L3 (ker_cube_L3core hS hker) hu (sq_one_of_orderOf_two_L3core hu2)
  obtain ⟨q, hq, hqa⟩ := hS.conj (a : GL (Fin 3) F) a.2 (coe_sq_one_L3core ha)
    (coe_ne_one_of_orderOf_L3core hu2)
  have ea : a = invL3core hS ⟨q, hq⟩ := Subtype.ext (by
    show (a : GL (Fin 3) F) = q * negDiag3 F * q⁻¹
    rw [← hqa]; group)
  subst ea
  rw [leviOfL3_eq_L3core hS (ker_central_L3core hker) (ker_cube_L3core hS hker)]
  refine ⟨isL3Levi_L3core hS hker ⟨q, hq⟩ hu2, fun c hc hcu hcC g hg hgu => ?_⟩
  obtain ⟨c', rfl⟩ := hc
  obtain ⟨g', rfl⟩ := hg
  exact centralizer_commute_L3core hS hker ⟨q, hq⟩ c' g' hcu hgu
    (Subgroup.mem_centralizer_iff.mp hcC)

theorem L3Shape.exists_of_mem_levi (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) {g : ↥S} {y : G}
    (hy : y ∈ leviOfL3 ψ.range (ψ (g * ⟨negDiag3 F, hS.neg_mem⟩ * g⁻¹))) :
    ∃ b : GL (Fin 2) F, b ∈ sl2Of Bl ∧ ∃ a : ↥S,
      (a : GL (Fin 3) F) = (g : GL (Fin 3) F) * blk b * (g : GL (Fin 3) F)⁻¹ ∧ ψ a = y := by
  rw [leviOfL3_eq_L3core hS (ker_central_L3core hker) (ker_cube_L3core hS hker) g] at hy
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
  exact ⟨(x : GL (Fin 2) F), x.2, phiConj_L3core hS g x, rfl, hx⟩

theorem L3Shape.mem_levi_of_exists (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) {g : ↥S} {b : GL (Fin 2) F}
    (hb : b ∈ sl2Of Bl) {a : ↥S}
    (ha : (a : GL (Fin 3) F) = (g : GL (Fin 3) F) * blk b * (g : GL (Fin 3) F)⁻¹) :
    ψ a ∈ leviOfL3 ψ.range (ψ (g * ⟨negDiag3 F, hS.neg_mem⟩ * g⁻¹)) := by
  rw [leviOfL3_eq_L3core hS (ker_central_L3core hker) (ker_cube_L3core hS hker) g]
  refine MonoidHom.mem_range.mpr ⟨⟨b, hb⟩, ?_⟩
  show ψ (phiConj_L3core hS g ⟨b, hb⟩) = ψ a
  congr 1
  exact Subtype.ext ha.symm

end CoreA

end CFSG.Quasithin.H13
