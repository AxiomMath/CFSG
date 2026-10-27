module

public import CFSG.Monster.VisQuot.MonoFlag
public import CFSG.Monster.VisQuot.FixModOmega

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisQuot

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Lifts CFSG.Monster.ScalarKernel CFSG.Monster.Visible
  CFSG.Monster.Visible.SignCompat CFSG.Monster.VisCert

@[expose] def Tsd : Subgroup MonoSD :=
  (CFSG.Monster.B.TwoA.Census.sylowSub.comap AutPerm.subtype).comap
    SemidirectProduct.rightHom

@[expose] def signPart (A : Subgroup MonoSD) : Submodule (ZMod 2) C where
  carrier := {c | SemidirectProduct.inl (Multiplicative.ofAdd (Submodule.Quotient.mk c)) ∈ A}
  add_mem' {a b} ha hb := by
    have h : SemidirectProduct.inl
        (Multiplicative.ofAdd (Submodule.Quotient.mk (a + b))) ∈ A := by
      have hsum : (Submodule.Quotient.mk (a + b) : C ⧸ ΩLine) =
          Submodule.Quotient.mk a + Submodule.Quotient.mk b := rfl
      rw [hsum, ofAdd_add, map_mul]
      exact A.mul_mem ha hb
    exact h
  zero_mem' := by
    change SemidirectProduct.inl (Multiplicative.ofAdd (Submodule.Quotient.mk (0 : C))) ∈ A
    rw [Submodule.Quotient.mk_zero, ofAdd_zero, map_one]
    exact A.one_mem
  smul_mem' s a ha := by
    rcases (show ∀ s : ZMod 2, s = 0 ∨ s = 1 by decide) s with rfl | rfl
    · simp
    · simpa using ha

theorem mem_Tsd {x : MonoSD} :
    x ∈ Tsd ↔ (x.right : Equiv.Perm (Fin 24)) ∈ CFSG.Monster.B.TwoA.Census.sylowSub :=
  Iff.rfl

theorem ΩC_mem_signPart (A : Subgroup MonoSD) : ΩC ∈ signPart A := by
  have hΩ : (Submodule.Quotient.mk ΩC : C ⧸ ΩLine) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (mem_ΩLine_iff.2 (Or.inr rfl))
  change SemidirectProduct.inl (Multiplicative.ofAdd (Submodule.Quotient.mk ΩC)) ∈ A
  rw [hΩ, ofAdd_zero, map_one]
  exact A.one_mem

theorem monoHom_apply_of_left {x : MonoSD} {a : C}
    (ha : x.left = Multiplicative.ofAdd (Submodule.Quotient.mk a)) (w : L2) :
    ((monoHom x : LinearMap.GeneralLinearGroup (ZMod 2) L2) : L2 →ₗ[ZMod 2] L2) w =
      modTwoEnd (gO a) (modTwoEnd (PO x.right) w) := by
  have hx : monoHom x = signQ (Multiplicative.ofAdd (Submodule.Quotient.mk a)) *
      permHom x.right := by
    rw [monoHom_apply, ha]
  rw [hx, signQ_mk, permHom_apply]
  change ((modTwoUnit (gO a) * modTwoUnit (PO x.right) :
    LinearMap.GeneralLinearGroup (ZMod 2) L2) : Module.End (ZMod 2) L2) w = _
  rw [Units.val_mul, Module.End.mul_apply, coe_modTwoUnit, coe_modTwoUnit]

theorem signPart_le_fixModΩ {A : Subgroup MonoSD} (hA : IsMulCommutative A) :
    signPart A ≤ fixModΩ (A.map SemidirectProduct.rightHom) := by
  intro c hc
  rw [mem_fixModΩ]
  intro p hp
  rw [Subgroup.mem_map] at hp
  obtain ⟨g, hgA, rfl⟩ := hp
  let n : Multiplicative (C ⧸ ΩLine) :=
    Multiplicative.ofAdd (Submodule.Quotient.mk c)
  have hnc : SemidirectProduct.inl n ∈ A := hc
  have hcommA : (⟨g, hgA⟩ : A) * ⟨SemidirectProduct.inl n, hnc⟩ =
      ⟨SemidirectProduct.inl n, hnc⟩ * ⟨g, hgA⟩ :=
    (isMulCommutative_iff.1 hA) _ _
  have hcomm : g * SemidirectProduct.inl n = SemidirectProduct.inl n * g :=
    congrArg (fun x : A => (x : MonoSD)) hcommA
  have hleft := congrArg SemidirectProduct.left hcomm
  have hleft' : g.left * permAct g.right n = n * g.left := by
    simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply, mul_one] using hleft
  have hleft'' : g.left * permAct g.right n = g.left * n := by
    rw [hleft', mul_comm]
  have hperm : permAct g.right n = n :=
    mul_left_cancel hleft''
  have hq : (Submodule.Quotient.mk (p := ΩLine) (permC g.right c) : C ⧸ ΩLine) =
      Submodule.Quotient.mk (p := ΩLine) c := by
    have h := congrArg Multiplicative.toAdd hperm
    simpa [n, permAct_mk] using h
  exact (Submodule.Quotient.eq (p := (ΩLine : Submodule (ZMod 2) C))).1 hq

theorem two_mul_card_eq (A : Subgroup MonoSD) :
    2 * Nat.card A = Nat.card (signPart A) *
      Nat.card (A.map SemidirectProduct.rightHom) := by
  let P : Subgroup AutPerm := A.map SemidirectProduct.rightHom
  let X : Submodule (ZMod 2) C := signPart A
  let K : Subgroup MonoSD := SemidirectProduct.inl.range ⊓ A
  have hΩX : ΩLine ≤ X := by
    rw [ΩLine, Submodule.span_singleton_le_iff_mem]
    exact ΩC_mem_signPart A
  have hcardΩ : Nat.card ΩLine = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_ΩLine, Nat.card_zmod]
    norm_num
  let f : ↥A →* AutPerm := SemidirectProduct.rightHom.domRestrict A
  have hfrange : f.range = P := by
    simp [f, P]
  have hfker : f.ker = SemidirectProduct.inl.range.subgroupOf A := by
    rw [MonoidHom.ker_domRestrict, SemidirectProduct.range_inl_eq_ker_rightHom]
  have hKcardKer : Nat.card K = Nat.card f.ker := by
    rw [hfker]
    have hmap : (SemidirectProduct.inl.range.subgroupOf A).map A.subtype =
        SemidirectProduct.inl.range ⊓ A := Subgroup.subgroupOf_map_subtype _ _
    rw [show K = SemidirectProduct.inl.range ⊓ A from rfl, ← hmap]
    change Nat.card ↥(Subgroup.map A.subtype (SemidirectProduct.inl.range.subgroupOf A)) =
      Nat.card ↥(SemidirectProduct.inl.range.subgroupOf A)
    exact Subgroup.card_map_of_injective A.subtype_injective
  have hA1 : Nat.card K * Nat.card P = Nat.card A := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [← hKcardKer, hfrange] at h
    simpa using h
  let Xsub : Subgroup (Multiplicative C) := (signPart A).toAddSubgroup.toSubgroup
  have hcardXsub : Nat.card ↥Xsub = Nat.card (signPart A) := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun c => ⟨Multiplicative.toAdd c.1,
          (Multiplicative.mem_toSubgroup (signPart A).toAddSubgroup c.1).1 c.2⟩
        invFun := fun c => ⟨Multiplicative.ofAdd c.1, by
          rw [Multiplicative.mem_toSubgroup]
          exact c.2⟩
        left_inv := fun c => Subtype.ext (by simp)
        right_inv := fun c => Subtype.ext (by simp) }
  let ψ : ↥Xsub →* K :=
    { toFun := fun c =>
        ⟨SemidirectProduct.inl (Multiplicative.ofAdd
            (Submodule.Quotient.mk (p := ΩLine) (Multiplicative.toAdd c.1))), by
          rw [Subgroup.mem_inf]
          exact ⟨⟨_, rfl⟩, c.2⟩⟩
      map_one' := Subtype.ext (by
        change SemidirectProduct.inl (Multiplicative.ofAdd
          (Submodule.Quotient.mk (p := ΩLine) (0 : C))) = 1
        rw [Submodule.Quotient.mk_zero, ofAdd_zero, map_one])
      map_mul' c d := Subtype.ext (by
        change SemidirectProduct.inl (Multiplicative.ofAdd
          (Submodule.Quotient.mk (p := ΩLine)
            (Multiplicative.toAdd (c * d)))) =
          SemidirectProduct.inl (Multiplicative.ofAdd
            (Submodule.Quotient.mk (p := ΩLine) (Multiplicative.toAdd c.1))) *
          SemidirectProduct.inl (Multiplicative.ofAdd
            (Submodule.Quotient.mk (p := ΩLine) (Multiplicative.toAdd d.1)))
        rw [toAdd_mul, Submodule.Quotient.mk_add, ofAdd_add, map_mul]) }
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨x, hxK⟩
    rw [Subgroup.mem_inf] at hxK
    obtain ⟨hxrange, hxA⟩ := hxK
    rw [MonoidHom.mem_range] at hxrange
    obtain ⟨n, hn⟩ := hxrange
    let q : C ⧸ ΩLine := Multiplicative.toAdd n
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective ΩLine q
    have hnq : Multiplicative.ofAdd q = n := ofAdd_toAdd n
    have hcA : c ∈ signPart A := by
      show SemidirectProduct.inl
        (Multiplicative.ofAdd (Submodule.Quotient.mk (p := ΩLine) c)) ∈ A
      rw [hc, hnq, hn]
      exact hxA
    let cX : ↥Xsub := ⟨Multiplicative.ofAdd c, by
      rw [Multiplicative.mem_toSubgroup]
      exact hcA⟩
    refine ⟨cX, ?_⟩
    apply Subtype.ext
    show SemidirectProduct.inl (Multiplicative.ofAdd
      (Submodule.Quotient.mk (p := ΩLine) (Multiplicative.toAdd cX.1))) = x
    rw [show (Multiplicative.toAdd cX.1 : C) = c from rfl, hc, hnq, hn]
  have hψ := Subgroup.card_ker_mul_card_of_surjective (f := ψ) hψsurj
  have hψker : Nat.card ψ.ker = 2 := by
    have hcard : Nat.card ψ.ker = Nat.card (ΩLine.submoduleOf (signPart A)) := by
      refine Nat.card_congr ?_
      exact
        { toFun := fun c => ⟨⟨Multiplicative.toAdd c.1.1, c.1.2⟩, by
            have h1 : (ψ c.1 : MonoSD) = 1 :=
              congrArg Subtype.val (MonoidHom.mem_ker.1 c.2)
            have h2 := SemidirectProduct.inl_injective h1
            have h3 : (Submodule.Quotient.mk (p := ΩLine)
                (Multiplicative.toAdd c.1.1)) = 0 := by
              simpa using congrArg Multiplicative.toAdd h2
            exact (Submodule.Quotient.mk_eq_zero ΩLine).1 h3⟩
          invFun := fun c =>
            let z : Multiplicative C := Multiplicative.ofAdd (c.1 : C)
            ⟨⟨z, by
                rw [Multiplicative.mem_toSubgroup]
                exact c.1.2⟩,
              by
                rw [MonoidHom.mem_ker]
                apply Subtype.ext
                change SemidirectProduct.inl (Multiplicative.ofAdd
                  (Submodule.Quotient.mk (p := ΩLine) (c.1 : C))) = 1
                have hcΩ : (c.1 : C) ∈ ΩLine := c.2
                rw [(Submodule.Quotient.mk_eq_zero ΩLine).2 hcΩ]
                simp⟩
          left_inv := fun c => Subtype.ext (Subtype.ext (by
            show Multiplicative.ofAdd (Multiplicative.toAdd c.1.1) = c.1.1
            exact ofAdd_toAdd c.1.1))
          right_inv := fun c => Subtype.ext (Subtype.ext (by
            show (Multiplicative.toAdd (Multiplicative.ofAdd (c.1 : C)) : C) = (c.1 : C)
            exact toAdd_ofAdd (c.1 : C))) }
    rw [hcard]
    calc Nat.card (ΩLine.submoduleOf (signPart A)) = Nat.card ΩLine :=
          Nat.card_congr (Submodule.submoduleOfEquivOfLe hΩX).toEquiv
      _ = 2 := hcardΩ
  have hX2 : 2 * Nat.card K = Nat.card (signPart A) := by
    rw [show 2 * Nat.card K = Nat.card ψ.ker * Nat.card K by rw [hψker]]
    exact hψ.trans hcardXsub
  calc 2 * Nat.card A = 2 * (Nat.card K * Nat.card P) := by rw [hA1]
    _ = (2 * Nat.card K) * Nat.card P := by ring
    _ = Nat.card X * Nat.card P := by rw [hX2]

theorem card_mul_card_le_of_fixBound (hFB : FixBound) {A : Subgroup MonoSD} (hAT : A ≤ Tsd)
    (hA : CFSG.Open.IsElemAbelian 2 A) {D : Submodule (ZMod 2) L2}
    (hfix : ∀ g ∈ A, ∀ w ∈ D,
      ((monoHom g : LinearMap.GeneralLinearGroup (ZMod 2) L2) : L2 →ₗ[ZMod 2] L2) w = w)
    (hsing : ∀ w ∈ D, qL w = 0) :
    Nat.card A * Nat.card D ≤ 2 ^ 14 := by
  let P : Subgroup AutPerm := A.map SemidirectProduct.rightHom
  let X : Submodule (ZMod 2) C := signPart A
  let Z : Submodule (ZMod 2) C := compatC X ⊓ fixModΩ P
  let W : Submodule (ZMod 2) C := commΩ P ⊔ X
  let D₁ : Submodule (ZMod 2) Cocode := (D ⊓ U1).map cocodeCoord
  let D₂ : Submodule (ZMod 2) C := (D ⊓ LinearMap.ker parity).map codeCoord ⊔ ΩLine
  have hP : ∀ p ∈ P, (p : Equiv.Perm (Fin 24)) ∈ CFSG.Monster.B.TwoA.Census.sylowSub := by
    intro p hp
    rw [Subgroup.mem_map] at hp
    obtain ⟨g, hgA, rfl⟩ := hp
    exact mem_Tsd.1 (hAT hgA)
  have hPe : CFSG.Open.IsElemAbelian 2 P := by
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      intro x y
      obtain ⟨p, hp⟩ := x
      obtain ⟨q, hq⟩ := y
      rw [Subgroup.mem_map] at hp hq
      obtain ⟨g, hgA, rfl⟩ := hp
      obtain ⟨h, hhA, rfl⟩ := hq
      apply Subtype.ext
      show SemidirectProduct.rightHom (g * h) = SemidirectProduct.rightHom (h * g)
      have hcomm : g * h = h * g :=
        congrArg (fun x : A => (x : MonoSD))
          ((isMulCommutative_iff.1 hA.1) ⟨g, hgA⟩ ⟨h, hhA⟩)
      rw [hcomm]
    · intro p hp
      rw [Subgroup.mem_map] at hp
      obtain ⟨g, hgA, rfl⟩ := hp
      rw [← map_pow, hA.2 g hgA, map_one]
  have hXΩ : ΩC ∈ X := ΩC_mem_signPart A
  have hXF : X ≤ fixModΩ P := signPart_le_fixModΩ hA.1
  have hΩZ : ΩLine ≤ Z := by
    rw [ΩLine, Submodule.span_singleton_le_iff_mem]
    exact ⟨ΩC_mem_compatC X, ΩC_mem_fixModΩ P⟩
  have hD₂_le_Z : D₂ ≤ Z := by
    intro c hc
    change c ∈ ((D ⊓ LinearMap.ker parity).map codeCoord ⊔ ΩLine) at hc
    rw [Submodule.mem_sup] at hc
    obtain ⟨c₁, hc₁, c₂, hc₂, hsum⟩ := hc
    have h₁ : c₁ ∈ Z := by
      rw [Submodule.mem_map] at hc₁
      obtain ⟨y, hy, rfl⟩ := hc₁
      rw [Submodule.mem_inf] at hy
      obtain ⟨hyD, hyp⟩ := hy
      change codeCoord y ∈ compatC X ⊓ fixModΩ P
      rw [Submodule.mem_inf]
      constructor
      · rw [mem_compatC]
        intro b hb
        let gb : MonoSD := SemidirectProduct.inl
          (Multiplicative.ofAdd (Submodule.Quotient.mk (p := ΩLine) b))
        have hgbA : gb ∈ A := hb
        have hfixb := hfix gb hgbA y hyD
        have hleft := monoHom_apply_of_left (x := gb) (a := b) (by rfl) y
        rw [hleft] at hfixb
        have hright : gb.right = 1 := rfl
        rw [hright, PO_one, modTwoEnd_one, Module.End.one_apply] at hfixb
        have hcocode := congrArg cocodeCoord hfixb
        have hyp0 : parity y = 0 := hyp
        rw [cocodeCoord_gO, hyp0, zero_smul, add_zero] at hcocode
        have hzero : (Submodule.Quotient.mk (p := C)
            ((b : Fin 24 → ZMod 2) * codeCoord y)) = 0 := by
          have h' : cocodeCoord y + 0 = cocodeCoord y +
              (Submodule.Quotient.mk (p := C)
                ((b : Fin 24 → ZMod 2) * codeCoord y)) := by
            simpa using hcocode
          exact (add_left_cancel h').symm
        rw [Submodule.Quotient.mk_eq_zero] at hzero
        simpa [mul_comm] using hzero
      · rw [mem_fixModΩ]
        intro p hp
        rw [Subgroup.mem_map] at hp
        obtain ⟨g, hgA, rfl⟩ := hp
        obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective ΩLine
          (Multiplicative.toAdd g.left)
        have ha' : g.left = Multiplicative.ofAdd (Submodule.Quotient.mk a) := by
          rw [ha, ofAdd_toAdd]
        have hfixg := hfix g hgA y hyD
        obtain ⟨s, hs⟩ := codeCoord_gO a (modTwoEnd (PO g.right) y)
        have hcode := congrArg codeCoord hfixg
        rw [monoHom_apply_of_left ha' y, hs, codeCoord_PO, parity_PO, hyp,
          zero_smul, add_zero] at hcode
        have hq : (Submodule.Quotient.mk (p := ΩLine)
              (permC g.right (codeCoord y)) : C ⧸ ΩLine) =
            Submodule.Quotient.mk (p := ΩLine) (codeCoord y) := by
          have hΩ : (Submodule.Quotient.mk (p := ΩLine) ΩC : C ⧸ ΩLine) = 0 :=
            (Submodule.Quotient.mk_eq_zero ΩLine).2 (mem_ΩLine_iff.2 (Or.inr rfl))
          have hΩsmul : (Submodule.Quotient.mk (p := ΩLine) (s • ΩC) :
              C ⧸ ΩLine) = 0 := by
            rw [Submodule.Quotient.mk_smul, hΩ, smul_zero]
          have h1 : (Submodule.Quotient.mk (p := ΩLine)
              (permC g.right (codeCoord y) + s • ΩC) : C ⧸ ΩLine) =
              Submodule.Quotient.mk (p := ΩLine) (codeCoord y) :=
            congrArg (fun z => Submodule.Quotient.mk (p := ΩLine) z) hcode
          calc Submodule.Quotient.mk (p := ΩLine) (permC g.right (codeCoord y))
              = Submodule.Quotient.mk (p := ΩLine) (permC g.right (codeCoord y)) +
                Submodule.Quotient.mk (p := ΩLine) (s • ΩC) := by
                  rw [hΩsmul, add_zero]
            _ = Submodule.Quotient.mk (p := ΩLine)
                (permC g.right (codeCoord y) + s • ΩC) :=
                  (Submodule.Quotient.mk_add (p := ΩLine)).symm
            _ = Submodule.Quotient.mk (p := ΩLine) (codeCoord y) := h1
        exact (Submodule.Quotient.eq (p := (ΩLine : Submodule (ZMod 2) C))).1 hq
    have h₂ : c₂ ∈ Z := hΩZ hc₂
    rw [← hsum]
    exact Z.add_mem h₁ h₂
  have hD₁_le : D₁ ≤ cocodeAnn (W ⊔ D₂) := by
    intro δ hδ
    rw [Submodule.mem_map] at hδ
    obtain ⟨u, hu, rfl⟩ := hδ
    rw [Submodule.mem_inf] at hu
    obtain ⟨huD, huU1⟩ := hu
    have huU1' := huU1
    rw [U1, Submodule.mem_inf] at huU1'
    have hΩ0 : pair ΩC (cocodeCoord u) = 0 := by
      change parity u = 0
      exact huU1'.2
    rw [mem_cocodeAnn]
    intro c hc
    change c ∈ (commΩ P ⊔ X) ⊔
      ((D ⊓ LinearMap.ker parity).map codeCoord ⊔ ΩLine) at hc
    rw [Submodule.mem_sup] at hc
    obtain ⟨c₁, hc₁, c₂, hc₂, hsum⟩ := hc
    have hc₁0 : pair c₁ (cocodeCoord u) = 0 := by
      change c₁ ∈ commΩ P ⊔ X at hc₁
      rw [Submodule.mem_sup] at hc₁
      obtain ⟨w₁, hw₁, w₂, hw₂, hsum₁⟩ := hc₁
      have hw₁0 : pair w₁ (cocodeCoord u) = 0 := by
        have hker : commΩ P ≤ LinearMap.ker (pairing.flip (cocodeCoord u)) := by
          rw [commΩ, Submodule.span_le]
          intro z hz
          rw [Set.mem_insert_iff] at hz
          rcases hz with rfl | hz
          · exact hΩ0
          · obtain ⟨p, hp, c', rfl⟩ := hz
            change pair (permC p c' - c') (cocodeCoord u) = 0
            have hpermD : permD p (cocodeCoord u) = cocodeCoord u := by
              obtain ⟨g, hgA, rfl⟩ := hp
              obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective ΩLine
                (Multiplicative.toAdd g.left)
              have ha' : g.left = Multiplicative.ofAdd (Submodule.Quotient.mk a) := by
                rw [ha, ofAdd_toAdd]
              have hfixg := hfix g hgA u huD
              rw [monoHom_apply_of_left ha' u] at hfixg
              have hcocode := congrArg cocodeCoord hfixg
              have huU1P : modTwoEnd (PO g.right) u ∈ U1 :=
                modTwoEnd_PO_mem_U1 g.right huU1
              have hcodeU : codeCoord (modTwoEnd (PO g.right) u) ∈ ΩLine :=
                huU1P.1
              have hprodC : ((a : Fin 24 → ZMod 2) *
                  (codeCoord (modTwoEnd (PO g.right) u) : Fin 24 → ZMod 2)) ∈ C := by
                rcases mem_ΩLine_iff.1 hcodeU with h0 | hΩ
                · rw [h0]
                  simp
                · rw [hΩ]
                  have hone : (a : Fin 24 → ZMod 2) * (ΩC : Fin 24 → ZMod 2) = a := by
                    funext i
                    simp [ΩC, Ω]
                  rw [hone]
                  exact a.2
              have hprod0 : (Submodule.Quotient.mk (p := C)
                  ((a : Fin 24 → ZMod 2) *
                    (codeCoord (modTwoEnd (PO g.right) u) : Fin 24 → ZMod 2))) =
                  0 := (Submodule.Quotient.mk_eq_zero C).2 hprodC
              rw [cocodeCoord_gO, cocodeCoord_PO_of_mem_U1 g.right huU1,
                parity_PO, huU1'.2, zero_smul, add_zero, hprod0, add_zero] at hcocode
              exact hcocode
            change (pairing.flip (cocodeCoord u)) (permC p c' - c') = 0
            rw [map_sub]
            have hpair : pair (permC p c') (cocodeCoord u) =
                pair c' (cocodeCoord u) := by
              calc pair (permC p c') (cocodeCoord u) =
                    pair (permC p c') (permD p (cocodeCoord u)) := by
                      nth_rewrite 1 [← hpermD]
                      rfl
                _ = pair c' (cocodeCoord u) :=
                      pair_permC_permD p c' (cocodeCoord u)
            change pair (permC p c') (cocodeCoord u) -
              pair c' (cocodeCoord u) = 0
            rw [hpair, sub_self]
        exact hker hw₁
      have hw₂0 : pair w₂ (cocodeCoord u) = 0 := by
        let gb : MonoSD := SemidirectProduct.inl
          (Multiplicative.ofAdd (Submodule.Quotient.mk (p := ΩLine) w₂))
        have hgbA : gb ∈ A := hw₂
        have hfixb := hfix gb hgbA u huD
        have hleft := monoHom_apply_of_left (x := gb) (a := w₂) (by rfl) u
        rw [hleft] at hfixb
        have hright : gb.right = 1 := rfl
        rw [hright, PO_one, modTwoEnd_one, Module.End.one_apply] at hfixb
        have hgo := modTwoEnd_gO_of_mem_U1 w₂ huU1
        rw [hfixb] at hgo
        have hzero : pair w₂ (cocodeCoord u) • twoΩCls = 0 := by
          have h' : u + 0 = u + pair w₂ (cocodeCoord u) • twoΩCls := by
            simpa using hgo
          exact (add_left_cancel h').symm
        rcases (show ∀ s : ZMod 2, s = 0 ∨ s = 1 by decide)
          (pair w₂ (cocodeCoord u)) with h | h
        · exact h
        · rw [h, one_smul] at hzero
          exact absurd hzero twoΩCls_mem_frameDelta.1
      rw [← hsum₁, pair_add_left, hw₁0, hw₂0, add_zero]
    have hc₂0 : pair c₂ (cocodeCoord u) = 0 := by
      change c₂ ∈ (D ⊓ LinearMap.ker parity).map codeCoord ⊔ ΩLine at hc₂
      rw [Submodule.mem_sup] at hc₂
      obtain ⟨d₁, hd₁, d₂, hd₂, hsum₂⟩ := hc₂
      have hd₁0 : pair d₁ (cocodeCoord u) = 0 := by
        rw [Submodule.mem_map] at hd₁
        obtain ⟨y, hy, rfl⟩ := hd₁
        rw [Submodule.mem_inf] at hy
        obtain ⟨hyD, hyp⟩ := hy
        rw [← polarBilin_of_mem_U1 huU1 hyp]
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
          hsing (u + y) (D.add_mem huD hyD), hsing u huD, hsing y hyD]
        simp
      have hd₂0 : pair d₂ (cocodeCoord u) = 0 := by
        rw [ΩLine, Submodule.mem_span_singleton] at hd₂
        obtain ⟨s, rfl⟩ := hd₂
        rw [pair_smul_left, hΩ0, mul_zero]
      rw [← hsum₂, pair_add_left, hd₁0, hd₂0, add_zero]
    rw [← hsum, pair_add_left, hc₁0, hc₂0, add_zero]
  have hdimD : Module.finrank (ZMod 2) D ≤
      Module.finrank (ZMod 2) D₁ + Module.finrank (ZMod 2) D₂ := by
    simpa [D₁, D₂] using finrank_le_of_singular hsing
  have hdimD₁ : Module.finrank (ZMod 2) D₁ +
      Module.finrank (ZMod 2) ↥(W ⊔ D₂) ≤ 12 := by
    have hmono := Submodule.finrank_mono hD₁_le
    have hann := finrank_cocodeAnn_add (W ⊔ D₂)
    omega
  have hdimD₂ : Module.finrank (ZMod 2) D₂ +
      Module.finrank (ZMod 2) ↥(W ⊔ Z) ≤
      Module.finrank (ZMod 2) Z + Module.finrank (ZMod 2) ↥(W ⊔ D₂) :=
    finrank_add_finrank_sup_le hD₂_le_Z W
  have hdim : Module.finrank (ZMod 2) D +
      Module.finrank (ZMod 2) ↥(W ⊔ Z) ≤ 12 + Module.finrank (ZMod 2) Z := by
    omega
  have hcardD : Nat.card D = 2 ^ Module.finrank (ZMod 2) D := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcardWZ : Nat.card ↥(W ⊔ Z) = 2 ^ Module.finrank (ZMod 2) ↥(W ⊔ Z) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcardZ : Nat.card Z = 2 ^ Module.finrank (ZMod 2) Z := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcard_wz : Nat.card D * Nat.card ↥(W ⊔ Z) ≤ 2 ^ 12 * Nat.card Z := by
    rw [hcardD, hcardWZ, hcardZ, ← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hFB' : Nat.card X * Nat.card P * 2 ^ 11 * Nat.card Z ≤
      2 ^ 14 * Nat.card ↥(W ⊔ Z) :=
    hFB P hP hPe X hXΩ hXF
  have htwo : 2 * Nat.card A = Nat.card X * Nat.card P := two_mul_card_eq A
  have h3 : Nat.card A * 2 ^ 12 * Nat.card Z ≤
      2 ^ 14 * Nat.card ↥(W ⊔ Z) := by
    calc Nat.card A * 2 ^ 12 * Nat.card Z =
          2 * Nat.card A * 2 ^ 11 * Nat.card Z := by ring
      _ ≤ 2 ^ 14 * Nat.card ↥(W ⊔ Z) := by
          rw [htwo]
          exact hFB'
  have hmul : Nat.card A * Nat.card D * Nat.card ↥(W ⊔ Z) ≤
      2 ^ 14 * Nat.card ↥(W ⊔ Z) := by
    calc Nat.card A * Nat.card D * Nat.card ↥(W ⊔ Z) =
          Nat.card A * (Nat.card D * Nat.card ↥(W ⊔ Z)) := by ring
      _ ≤ Nat.card A * (2 ^ 12 * Nat.card Z) := Nat.mul_le_mul_left _ hcard_wz
      _ = Nat.card A * 2 ^ 12 * Nat.card Z := by ring
      _ ≤ 2 ^ 14 * Nat.card ↥(W ⊔ Z) := h3
  have hpos : 0 < Nat.card ↥(W ⊔ Z) :=
    Finite.card_pos_iff.mpr ⟨⟨0, (W ⊔ Z).zero_mem⟩⟩
  exact Nat.le_of_mul_le_mul_right hmul hpos

end CFSG.Monster.VisQuot

