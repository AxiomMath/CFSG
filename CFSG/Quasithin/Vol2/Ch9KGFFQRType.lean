module

public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.H13.A7Nat1238QTabA314

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Quasithin

section Tools

theorem nonempty_centerQuot_equiv {P Q : Type*} [Group P] [Group Q] (hP : Group.IsPerfect P)
    (f : P →* Q) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center P) :
    Nonempty (P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q) := by
  have hc : Subgroup.center P = ((QuotientGroup.mk' (Subgroup.center Q)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (CFSG.LocalCores.comap_center_eq_of_perfect hP f hf hker).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

theorem nonempty_centerQuot_equiv_simple {X Q : Type*} [Group X] [Group Q]
    (hX : CFSG.IsQuasisimple X) (f : X →* Q) (hf : Function.Surjective f) (hQ : IsSimpleGroup Q) :
    Nonempty (X ⧸ Subgroup.center X ≃* Q) := by
  have htriv : ¬ f.ker = ⊤ := by
    intro h
    obtain ⟨q, hq⟩ := exists_ne (1 : Q)
    obtain ⟨x, rfl⟩ := hf q
    exact hq (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
  have hker : f.ker ≤ Subgroup.center X :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hX f.normal_ker).resolve_left htriv
  have hZQ : Subgroup.center Q = ⊥ := by
    have := hQ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      apply htriv
      have hc : commutator X ≤ f.ker := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top (f b)) (f a))
      exact top_le_iff.mp ((Group.isPerfect_def.mp hX.1).symm.le.trans hc)
  obtain ⟨e⟩ := nonempty_centerQuot_equiv hX.1 f hf hker
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZQ).trans QuotientGroup.quotientBot)⟩

theorem center_centerQuot_eq_bot {Q : Type*} [Group Q]
    (hp : Group.IsPerfect (Q ⧸ Subgroup.center Q)) :
    Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ := by
  obtain ⟨hsup, hP, hsurj⟩ :=
    CFSG.LocalCores.central_extension_derived (Subgroup.center Q) le_rfl hp
  set P := commutator Q with hPdef
  set f : ↥P →* Q ⧸ Subgroup.center Q := (QuotientGroup.mk' (Subgroup.center Q)).comp P.subtype
    with hf
  have hker : f.ker ≤ Subgroup.center ↥P := by
    intro x hx
    have hx' : (x : Q) ∈ Subgroup.center Q :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx' y)
  have hc := CFSG.LocalCores.comap_center_eq_of_perfect hP f hsurj hker
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨p, rfl⟩ := hsurj z
  have hpP : p ∈ Subgroup.center ↥P := by
    rw [← hc]
    exact hz
  have hpQ : (p : Q) ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    have hq : q ∈ P ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top q
    obtain ⟨a, ha, c, hc', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hq
    have h1 : a * (p : Q) = p * a :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hpP ⟨a, ha⟩)
    have h2 : c * (p : Q) = p * c := (Subgroup.mem_center_iff.mp hc' p).symm
    calc a * c * p = a * (c * p) := mul_assoc _ _ _
      _ = a * (p * c) := by rw [h2]
      _ = a * p * c := (mul_assoc _ _ _).symm
      _ = p * a * c := by rw [h1]
      _ = p * (a * c) := mul_assoc _ _ _
  show (QuotientGroup.mk' (Subgroup.center Q)) (p : Q) ∈ ⊥
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hpQ

theorem nonempty_centerQuot_equiv_of_center {X M : Type*} [Group X] [Group M] (e : X ≃* M)
    (hM : Subgroup.center M = ⊥) : Nonempty (X ⧸ Subgroup.center X ≃* M) := by
  have hX : Subgroup.center X = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [hM] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hX).trans QuotientGroup.quotientBot).trans e⟩

theorem nonempty_centerQuot_equiv_centerQuot {X Q : Type*} [Group X] [Group Q]
    (hX : Group.IsPerfect X) (e : X ≃* Q ⧸ Subgroup.center Q) :
    Nonempty (X ⧸ Subgroup.center X ≃* Q ⧸ Subgroup.center Q) := by
  have hp : Group.IsPerfect (Q ⧸ Subgroup.center Q) := by
    have := hX
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact nonempty_centerQuot_equiv_of_center e (center_centerQuot_eq_bot hp)

theorem oddCore_le_center_of_quasisimple {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) : CFSG.oddCore X ≤ Subgroup.center X := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (CFSG.oddCore_normal X) with h | h
  · exfalso
    have hs := A312.oddCore_isSolvable X
    rw [h] at hs
    exact H13.A7.not_isSolvable_of_isQuasisimple_qtab hq
      (Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).toMonoidHom)
        Subgroup.topEquiv.surjective)
  · exact h

end Tools

section Bar

variable {G : Type} [Group G] [Finite G]

theorem nonempty_centerQuot_modO2Image {H L : Subgroup G} (hL : L ∈ cComp H)
    (hq : CFSG.IsQuasisimple ↥L) :
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
      ↥(modO2Image H L) ⧸ Subgroup.center ↥(modO2Image H L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have hc : CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hn with h | h
    · exfalso
      apply not_isSolvable_of_mem_cComp hL
      have hK2 : IsPGroup 2 ↥L := fun g => by
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := ↥L) (p := 2)) ⟨g, h ▸ Subgroup.mem_top g⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
      have := hK2.isNilpotent
      infer_instance
    · exact h
  obtain ⟨e⟩ := modO2_mulEquiv hL
  have hcen := (CFSG.LocalCores.quasisimple_central_quotient hq _ hc).2.2
  have e₁ : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientQuotientEquivQuotient _ _ hc)
  have e₂ : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      ↥(modO2Image H L) ⧸ Subgroup.center ↥(modO2Image H L) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  exact ⟨e₁.symm.trans e₂⟩

end Bar

@[expose] def A314Type (S : Type) [Group S] : Prop :=
  IsPSL 3 2 2 S ∨ IsPSp4 2 2 S ∨ IsG2 2 2 S ∨ Is3D4 2 2 S ∨ IsAlt 7 S ∨ IsPSL 2 5 2 S ∨
    (∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ IsPSL 2 p 1 S) ∨ IsPSL 3 5 1 S ∨ IsPSU 3 5 1 S ∨
    IsSporadic .M22 S ∨ IsSporadic .M23 S ∨ IsSporadic .J1 S ∨ IsSporadic .J2 S ∨
    IsSporadic .J4 S ∨ IsSporadic .HS S ∨ IsSporadic .Ru S

theorem A314Type.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : A314Type S') : A314Type S := by
  have hN : ∀ {M : Type} [Group M], Nonempty (S' ≃* M) → Nonempty (S ≃* M) :=
    fun ⟨e'⟩ => ⟨e.trans e'⟩
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨a, K, k1, k2, hK, he⟩ := h
    exact Or.inl ⟨a, K, k1, k2, hK, hN he⟩
  · obtain ⟨a, K, k1, k2, hK, he⟩ := h
    exact Or.inr (Or.inl ⟨a, K, k1, k2, hK, hN he⟩)
  · obtain ⟨a, K, k1, k2, hK, he⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨a, K, k1, k2, hK, hN he⟩))
  · obtain ⟨a, K, k1, k2, hK, σ, hσ, he⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, K, k1, k2, hK, σ, hσ, hN he⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hN h)))))
  · obtain ⟨a, K, k1, k2, hK, he⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, K, k1, k2, hK, hN he⟩)))))
  · obtain ⟨p, hp, hp7, a, K, k1, k2, hK, he⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, hp, hp7, a, K, k1, k2, hK, hN he⟩))))))
  · obtain ⟨a, K, k1, k2, hK, he⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, K, k1, k2, hK, hN he⟩)))))))
  · obtain ⟨a, K, k1, k2, hK, he⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨a, K, k1, k2, hK, hN he⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hN h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (hN h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl (hN h))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl (hN h)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl (hN h))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hN h)))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hN h)))))))))))))))

section Intro

variable {S : Type} [Group S]

theorem A314Type.psl34 (h : IsPSL 3 2 2 S) : A314Type S :=
  Or.inl h

theorem A314Type.sp44 (h : IsPSp4 2 2 S) : A314Type S :=
  Or.inr (Or.inl h)

theorem A314Type.g24 (h : IsG2 2 2 S) : A314Type S :=
  Or.inr (Or.inr (Or.inl h))

theorem A314Type.d43 (h : Is3D4 2 2 S) : A314Type S :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem A314Type.alt7 (h : IsAlt 7 S) : A314Type S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem A314Type.psl225 (h : IsPSL 2 5 2 S) : A314Type S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem A314Type.psl2p (h : ∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ IsPSL 2 p 1 S) : A314Type S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem A314Type.psl35 (h : IsPSL 3 5 1 S) : A314Type S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem A314Type.psu35 (h : IsPSU 3 5 1 S) : A314Type S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

theorem A314Type.m22 (h : IsSporadic .M22 S) : A314Type S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))

theorem A314Type.m23 (h : IsSporadic .M23 S) : A314Type S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))

theorem A314Type.j1 (h : IsSporadic .J1 S) : A314Type S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    h)))))))))))

theorem A314Type.j2 (h : IsSporadic .J2 S) : A314Type S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl h))))))))))))

theorem A314Type.j4 (h : IsSporadic .J4 S) : A314Type S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl h)))))))))))))

theorem A314Type.hs (h : IsSporadic .HS S) : A314Type S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl h))))))))))))))

theorem A314Type.ru (h : IsSporadic .Ru S) : A314Type S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr h))))))))))))))

end Intro

end CFSG.Quasithin.H13.Ch9.KGFF
