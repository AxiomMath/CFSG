module

public import CFSG.Permutation.FiveTransitive.SharpFourBound

public section

namespace CFSG

namespace FiveTransitive.Research.HallSylowNormalizer

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
variable {p k : ℕ} [Fact p.Prime]

@[expose] abbrev FixedEmbedding (P : Subgroup G) (k : ℕ) :=
  Fin k ↪ MulAction.fixedPoints P X

@[expose] def FixedEmbedding.toAmbient (P : Subgroup G)
    (a : FixedEmbedding (X := X) P k) : Fin k ↪ X :=
  a.trans (Function.Embedding.subtype _)

@[simp] theorem FixedEmbedding.toAmbient_apply (P : Subgroup G)
    (a : FixedEmbedding (X := X) P k) (i : Fin k) :
    a.toAmbient P i = (a i : X) := rfl

private def IsSylowAtFixedEmbedding (P : Subgroup G)
    (a : FixedEmbedding (X := X) P k) : Prop :=
  ∃ Q : Sylow p (MulAction.stabilizer G (a.toAmbient P)),
    Subgroup.map (MulAction.stabilizer G (a.toAmbient P)).subtype
      (Q : Subgroup (MulAction.stabilizer G (a.toAmbient P))) = P

@[expose] def ambientSylow (e : Fin k ↪ X)
    (Q : Sylow p (MulAction.stabilizer G e)) : Subgroup G :=
  Subgroup.map (MulAction.stabilizer G e).subtype
    (Q : Subgroup (MulAction.stabilizer G e))

theorem ambientSylow_le_stabilizer (e : Fin k ↪ X)
    (Q : Sylow p (MulAction.stabilizer G e)) :
    ambientSylow e Q ≤ MulAction.stabilizer G e := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := hg
  exact q.property

private theorem ambientSylow_card (e : Fin k ↪ X)
    (Q : Sylow p (MulAction.stabilizer G e)) :
    Nat.card (ambientSylow e Q) = Nat.card (Q : Subgroup
      (MulAction.stabilizer G e)) := by
  symm
  exact Nat.card_congr
    ((Q : Subgroup (MulAction.stabilizer G e)).equivMapOfInjective
      (MulAction.stabilizer G e).subtype Subtype.coe_injective).toEquiv

private theorem ambientSylow_isSylowAtFixedEmbedding
    (htrans : MulAction.IsMultiplyPretransitive G X k)
    (e : Fin k ↪ X) (Q : Sylow p (MulAction.stabilizer G e))
    (a : FixedEmbedding (X := X) (ambientSylow e Q) k) :
    IsSylowAtFixedEmbedding (p := p) (ambientSylow e Q) a := by
  classical
  let P : Subgroup G := ambientSylow e Q
  let aX : Fin k ↪ X := a.toAmbient P
  have hP_le : P ≤ MulAction.stabilizer G aX := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Function.Embedding.ext
    intro i
    change g • (a i : X) = (a i : X)
    exact (a i).property ⟨g, hg⟩
  letI : MulAction.IsMultiplyPretransitive G X k := htrans
  obtain ⟨x, hx⟩ := htrans.exists_smul_eq e aX
  have hstabCard : Nat.card (MulAction.stabilizer G aX) =
      Nat.card (MulAction.stabilizer G e) := by
    symm
    exact Nat.card_congr
      (MulAction.stabilizerEquivStabilizer hx.symm).toEquiv
  have hsubCard : Nat.card (P.subgroupOf (MulAction.stabilizer G aX)) =
      p ^ (Nat.card (MulAction.stabilizer G aX)).factorization p := by
    calc
      Nat.card (P.subgroupOf (MulAction.stabilizer G aX)) = Nat.card P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le).toEquiv
      _ = Nat.card (Q : Subgroup (MulAction.stabilizer G e)) :=
        ambientSylow_card e Q
      _ = p ^ (Nat.card (MulAction.stabilizer G e)).factorization p :=
        Q.card_eq_multiplicity
      _ = p ^ (Nat.card (MulAction.stabilizer G aX)).factorization p := by
        rw [hstabCard]
  let Qa : Sylow p (MulAction.stabilizer G aX) :=
    Sylow.ofCard (P.subgroupOf (MulAction.stabilizer G aX)) hsubCard
  refine ⟨Qa, ?_⟩
  change Subgroup.map (MulAction.stabilizer G aX).subtype
      (P.subgroupOf (MulAction.stabilizer G aX)) = P
  exact Subgroup.map_subgroupOf_eq_of_le hP_le

private theorem exists_mem_normalizer_maps_fixedEmbedding
    (htrans : MulAction.IsMultiplyPretransitive G X k)
    (P : Subgroup G)
    (hsylow : ∀ a : FixedEmbedding (X := X) P k,
      IsSylowAtFixedEmbedding (p := p) P a)
    (a b : FixedEmbedding (X := X) P k) :
    ∃ z : G, z ∈ Subgroup.normalizer (P : Set G) ∧
      ∀ i, z • (a i : X) = (b i : X) := by
  classical
  let aX : Fin k ↪ X := a.toAmbient P
  let bX : Fin k ↪ X := b.toAmbient P
  letI : MulAction.IsMultiplyPretransitive G X k := htrans
  obtain ⟨x, hx⟩ := htrans.exists_smul_eq aX bX
  have hxba : bX = x • aX := hx.symm
  obtain ⟨Qa, hQa⟩ := hsylow a
  obtain ⟨Qb, hQb⟩ := hsylow b
  let E : MulAction.stabilizer G aX ≃*
      MulAction.stabilizer G bX :=
    MulAction.stabilizerEquivStabilizer hxba
  have hEsurjective : Function.Surjective E.toMonoidHom := E.surjective
  let Qx : Sylow p (MulAction.stabilizer G bX) :=
    Sylow.mapSurjective (f := E.toMonoidHom) hEsurjective Qa
  obtain ⟨y, hy⟩ :=
    MulAction.IsPretransitive.exists_smul_eq
      (M := MulAction.stabilizer G bX)
      (α := Sylow p (MulAction.stabilizer G bX)) Qx Qb
  let z : G := (y : G) * x
  have hQxAmbient :
      Subgroup.map (MulAction.stabilizer G bX).subtype
          (Qx : Subgroup (MulAction.stabilizer G bX)) =
        Subgroup.map (MulAut.conj x).toMonoidHom P := by
    dsimp only [Qx]
    change Subgroup.map (MulAction.stabilizer G bX).subtype
        (Subgroup.map E.toMonoidHom
          (Qa : Subgroup (MulAction.stabilizer G aX))) =
      Subgroup.map (MulAut.conj x).toMonoidHom P
    calc
      Subgroup.map (MulAction.stabilizer G bX).subtype
          (Subgroup.map E.toMonoidHom
            (Qa : Subgroup (MulAction.stabilizer G aX))) =
          Subgroup.map (MulAut.conj x).toMonoidHom
            (Subgroup.map (MulAction.stabilizer G aX).subtype
              (Qa : Subgroup (MulAction.stabilizer G aX))) := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
      _ = Subgroup.map (MulAut.conj x).toMonoidHom P :=
        congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hQa
  have hyAmbient :
      Subgroup.map (MulAut.conj (y : G)).toMonoidHom
          (Subgroup.map (MulAction.stabilizer G bX).subtype
            (Qx : Subgroup (MulAction.stabilizer G bX))) = P := by
    calc
      Subgroup.map (MulAut.conj (y : G)).toMonoidHom
          (Subgroup.map (MulAction.stabilizer G bX).subtype
            (Qx : Subgroup (MulAction.stabilizer G bX))) =
          Subgroup.map (MulAction.stabilizer G bX).subtype
            ((y • Qx : Sylow p (MulAction.stabilizer G bX)) :
              Subgroup (MulAction.stabilizer G bX)) := by
            change
              Subgroup.map (MulAut.conj (y : G)).toMonoidHom
                  (Subgroup.map (MulAction.stabilizer G bX).subtype
                    (Qx : Subgroup (MulAction.stabilizer G bX))) =
                Subgroup.map (MulAction.stabilizer G bX).subtype
                  (Subgroup.map (MulAut.conj y).toMonoidHom
                    (Qx : Subgroup (MulAction.stabilizer G bX)))
            rw [Subgroup.map_map, Subgroup.map_map]
            congr 1
      _ = Subgroup.map (MulAction.stabilizer G bX).subtype
          (Qb : Subgroup (MulAction.stabilizer G bX)) := by rw [hy]
      _ = P := hQb
  refine ⟨z, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Subgroup.map (MulAut.conj z).toMonoidHom P = P
    calc
      Subgroup.map (MulAut.conj z).toMonoidHom P =
          Subgroup.map (MulAut.conj (y : G)).toMonoidHom
            (Subgroup.map (MulAut.conj x).toMonoidHom P) := by
        rw [Subgroup.map_map]
        congr 1
        ext q
        dsimp only [z]
        simp only [MonoidHom.coe_comp, Function.comp_apply]
        change ((y : G) * x) * q * ((y : G) * x)⁻¹ =
          (y : G) * (x * q * x⁻¹) * (y : G)⁻¹
        group
      _ = Subgroup.map (MulAut.conj (y : G)).toMonoidHom
          (Subgroup.map (MulAction.stabilizer G bX).subtype
            (Qx : Subgroup (MulAction.stabilizer G bX))) := by
        rw [hQxAmbient]
      _ = P := hyAmbient
  · intro i
    have hyFix : (y : G) • bX = bX := y.property
    have hyi := congrArg (fun c : Fin k ↪ X => c i) hyFix
    have hxi := congrArg (fun c : Fin k ↪ X => c i) hx
    change ((y : G) * x) • (a i : X) = (b i : X)
    rw [mul_smul]
    change (y : G) • (x • aX i) = bX i
    rw [show x • aX i = bX i by
      simpa [Function.Embedding.smul_apply] using hxi]
    simpa [Function.Embedding.smul_apply] using hyi

theorem exists_mem_normalizer_ambientSylow_maps
    (htrans : MulAction.IsMultiplyPretransitive G X k)
    (e : Fin k ↪ X) (Q : Sylow p (MulAction.stabilizer G e))
    (a b : FixedEmbedding (X := X) (ambientSylow e Q) k) :
    ∃ z : G, z ∈ Subgroup.normalizer (ambientSylow e Q : Set G) ∧
      ∀ i, z • (a i : X) = (b i : X) := by
  apply exists_mem_normalizer_maps_fixedEmbedding (p := p)
    htrans (ambientSylow e Q)
  exact ambientSylow_isSylowAtFixedEmbedding htrans e Q

end FiveTransitive.Research.HallSylowNormalizer

end CFSG
