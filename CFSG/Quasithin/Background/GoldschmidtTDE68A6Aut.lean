module

public import CFSG.Quasithin.Background.GoldschmidtTDE68A6Cent
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8A6
public import CFSG.Quasithin.Background.GoldschmidtTDE68Ind

public section

namespace CFSG.Quasithin.E6.Alt.A6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.Unc25A6 CFSG.Quasithin.E6.Bar

theorem conjAut_mul (a b : ↥A6Models.autA6) : conjAut (a * b) = conjAut a * conjAut b := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  change ((a : P10) * (b : P10)) * (x : P10) * ((a : P10) * (b : P10))⁻¹ =
    (a : P10) * ((b : P10) * (x : P10) * (b : P10)⁻¹) * (a : P10)⁻¹
  group

theorem conjAut_one : conjAut (1 : ↥A6Models.autA6) = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  change ((1 : P10)) * (x : P10) * ((1 : P10))⁻¹ = (x : P10)
  group

theorem conjAut_eq_one_iff (a : ↥A6Models.autA6) : conjAut a = 1 ↔ a = 1 := by
  rw [← conjAut_one]
  exact conjAut_injective.eq_iff

theorem comm_of_conj_comm (a : ↥A6Models.autA6) (d : X0)
    (h : conjAut a * MulAut.conj d = MulAut.conj d * conjAut a) :
    (a : P10) * (d : P10) = (d : P10) * (a : P10) := by
  have hx : ∀ x : X0, (a : P10) * ((d : P10) * (x : P10) * (d : P10)⁻¹) * (a : P10)⁻¹ =
      (d : P10) * ((a : P10) * (x : P10) * (a : P10)⁻¹) * (d : P10)⁻¹ := fun x =>
    congrArg (fun f : MulAut X0 => ((f x : X0) : P10)) h
  have hd' : (d : P10) ∈ A6Models.autA6 := psl29_le_autA6 d.2
  have hc : ((d : P10) * (a : P10))⁻¹ * ((a : P10) * (d : P10)) ∈ A6Models.autA6 :=
    A6Models.autA6.mul_mem (A6Models.autA6.inv_mem (A6Models.autA6.mul_mem hd' a.2))
      (A6Models.autA6.mul_mem a.2 hd')
  have h1 := centralizer_psl29 hc (fun x hxP => by
    have hx' := hx ⟨x, hxP⟩
    generalize (a : P10) = A at hx' hc ⊢
    generalize (d : P10) = B at hx' hc ⊢
    have hx'' : (A * B) * x * (A * B)⁻¹ = (B * A) * x * (B * A)⁻¹ := by
      calc (A * B) * x * (A * B)⁻¹ = A * (B * x * B⁻¹) * A⁻¹ := by group
        _ = B * (A * x * A⁻¹) * B⁻¹ := hx'
        _ = (B * A) * x * (B * A)⁻¹ := by group
    have e1 : (A * B) * x = (B * A) * x * (B * A)⁻¹ * (A * B) := by
      calc (A * B) * x = ((A * B) * x * (A * B)⁻¹) * (A * B) := by group
        _ = ((B * A) * x * (B * A)⁻¹) * (A * B) := by rw [hx'']
    calc (B * A)⁻¹ * (A * B) * x = (B * A)⁻¹ * ((A * B) * x) := by group
      _ = (B * A)⁻¹ * ((B * A) * x * (B * A)⁻¹ * (A * B)) := by rw [e1]
      _ = x * ((B * A)⁻¹ * (A * B)) := by group)
  calc (a : P10) * (d : P10)
      = (d : P10) * (a : P10) * (((d : P10) * (a : P10))⁻¹ * ((a : P10) * (d : P10))) := by group
    _ = (d : P10) * (a : P10) := by rw [h1, mul_one]

theorem conj_comm_of_comm (a : ↥A6Models.autA6) (d : X0)
    (h : (a : P10) * (d : P10) = (d : P10) * (a : P10)) :
    conjAut a * MulAut.conj d = MulAut.conj d * conjAut a := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  change (a : P10) * ((d : P10) * (x : P10) * (d : P10)⁻¹) * (a : P10)⁻¹ =
    (d : P10) * ((a : P10) * (x : P10) * (a : P10)⁻¹) * (d : P10)⁻¹
  calc (a : P10) * ((d : P10) * (x : P10) * (d : P10)⁻¹) * (a : P10)⁻¹
      = ((a : P10) * (d : P10)) * (x : P10) * ((a : P10) * (d : P10))⁻¹ := by group
    _ = ((d : P10) * (a : P10)) * (x : P10) * ((d : P10) * (a : P10))⁻¹ := by rw [h]
    _ = (d : P10) * ((a : P10) * (x : P10) * (a : P10)⁻¹) * (d : P10)⁻¹ := by group

theorem mem_invSet_iff (β : MulAut X0) :
    β ∈ InvSet Dsub ↔ ∃ a : ↥A6Models.autA6, conjAut a = β ∧ code (a : P10) ∈ invCentD := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨a, rfl⟩ := conjAut_surjective β
    refine ⟨a, rfl, ?_⟩
    have ha1 : a ≠ 1 := fun h => h1 ((conjAut_eq_one_iff a).2 h)
    have ha2 : a * a = 1 := by
      have : conjAut (a * a) = conjAut 1 := by rw [conjAut_mul, conjAut_one, h2]
      exact conjAut_injective this
    have hcomm : ∀ d ∈ Dsub, (a : P10) * (d : P10) = (d : P10) * (a : P10) := fun d hd =>
      comm_of_conj_comm a d (h3 d hd)
    unfold invCentD
    rw [List.mem_filter]
    refine ⟨code_mem_autL a.2, ?_⟩
    have e1 : (Core.cmul (code (a : P10)) (code (a : P10)) == Core.cid) = true := by
      rw [beq_iff_eq, ← code_mul, ← code_one]
      exact congrArg code (congrArg Subtype.val ha2)
    have e2 : (code (a : P10) != Core.cid) = true := by
      rw [bne_iff_ne, ne_eq, ← code_one]
      intro h
      exact ha1 (Subtype.ext (code_injective h))
    have e3 : (Core.dLit.all fun d => Core.cmul (code (a : P10)) d ==
        Core.cmul d (code (a : P10))) = true := by
      rw [List.all_eq_true]
      intro c hc
      obtain ⟨y, hy, rfl⟩ := exists_Dsub_of_code hc
      rw [beq_iff_eq, ← code_mul, ← code_mul, hcomm y hy]
    simp only [e1, e2, e3, Bool.and_self]
  · rintro ⟨a, rfl, hmem⟩
    unfold invCentD at hmem
    rw [List.mem_filter] at hmem
    have hp := hmem.2
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true] at hp
    obtain ⟨⟨hsq, hne⟩, hall⟩ := hp
    have ha1 : a ≠ 1 := fun h => hne (by rw [← code_one]; exact congrArg code (by rw [h]; rfl))
    have ha2 : a * a = 1 := by
      apply Subtype.ext
      apply code_injective
      rw [Subgroup.coe_mul, code_mul, hsq, Subgroup.coe_one, code_one]
    have hcomm : ∀ d ∈ Dsub, (a : P10) * (d : P10) = (d : P10) * (a : P10) := by
      intro d hd
      apply code_injective
      rw [code_mul, code_mul]
      exact hall _ ((mem_Dsub d).1 hd)
    refine ⟨fun h => ha1 ((conjAut_eq_one_iff a).1 h), ?_,
      fun d hd => conj_comm_of_comm a d (hcomm d hd)⟩
    rw [← conjAut_mul, ha2, conjAut_one]

end CFSG.Quasithin.E6.Alt.A6
