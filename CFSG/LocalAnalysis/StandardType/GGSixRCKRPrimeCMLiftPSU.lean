module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMRestrict
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockCore
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUBlock

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.TableCRes

open scoped commutatorElement

theorem rckPSU_conj_mem_SU {n g : ℕ} {t : GL (Fin n) (PSUF g)}
    (ht : t ∈ GUsub (PSUσ g) n) {u : GL (Fin n) (PSUF g)}
    (hu : u ∈ Unitary.SU (PSUσ g) n) :
    t * u * t⁻¹ ∈ Unitary.SU (PSUσ g) n := by
  rw [Unitary.mem_SU] at hu ⊢
  obtain ⟨hudet, huiso⟩ := hu
  refine ⟨?_, ?_⟩
  · have hut : Matrix.GeneralLinearGroup.det u = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hudet, Units.val_one]
    have hdet : Matrix.GeneralLinearGroup.det (t * u * t⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hut, mul_one, mul_inv_cancel]
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Units.val hdet
  · have htI : Unitary.conjTr (PSUσ g) (t : Matrix (Fin n) (Fin n) (PSUF g)) *
        Unitary.antidiag n * (t : Matrix (Fin n) (Fin n) (PSUF g)) = Unitary.antidiag n :=
      mem_GUsub_iff.mp ht
    have htiI : Unitary.conjTr (PSUσ g) ((t⁻¹ : GL (Fin n) (PSUF g)) :
          Matrix (Fin n) (Fin n) (PSUF g)) * Unitary.antidiag n *
          ((t⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
        Unitary.antidiag n :=
      mem_GUsub_iff.mp (Subgroup.inv_mem _ ht)
    rw [Units.val_mul, Units.val_mul, Unitary.conjTr_mul, Unitary.conjTr_mul]
    calc Unitary.conjTr (PSUσ g) ((t⁻¹ : GL (Fin n) (PSUF g)) :
            Matrix (Fin n) (Fin n) (PSUF g)) *
          (Unitary.conjTr (PSUσ g) (u : Matrix (Fin n) (Fin n) (PSUF g)) *
            Unitary.conjTr (PSUσ g) (t : Matrix (Fin n) (Fin n) (PSUF g))) *
          Unitary.antidiag n *
          ((t : Matrix (Fin n) (Fin n) (PSUF g)) * (u : Matrix (Fin n) (Fin n) (PSUF g)) *
            ((t⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)))
        = Unitary.conjTr (PSUσ g) ((t⁻¹ : GL (Fin n) (PSUF g)) :
              Matrix (Fin n) (Fin n) (PSUF g)) *
            Unitary.conjTr (PSUσ g) (u : Matrix (Fin n) (Fin n) (PSUF g)) *
            (Unitary.conjTr (PSUσ g) (t : Matrix (Fin n) (Fin n) (PSUF g)) *
              Unitary.antidiag n * (t : Matrix (Fin n) (Fin n) (PSUF g))) *
            (u : Matrix (Fin n) (Fin n) (PSUF g)) *
            ((t⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) := by
          noncomm_ring
      _ = Unitary.conjTr (PSUσ g) ((t⁻¹ : GL (Fin n) (PSUF g)) :
              Matrix (Fin n) (Fin n) (PSUF g)) *
            Unitary.conjTr (PSUσ g) (u : Matrix (Fin n) (Fin n) (PSUF g)) *
            Unitary.antidiag n * (u : Matrix (Fin n) (Fin n) (PSUF g)) *
            ((t⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) := by
          rw [htI]
      _ = Unitary.conjTr (PSUσ g) ((t⁻¹ : GL (Fin n) (PSUF g)) :
              Matrix (Fin n) (Fin n) (PSUF g)) *
            (Unitary.conjTr (PSUσ g) (u : Matrix (Fin n) (Fin n) (PSUF g)) *
              Unitary.antidiag n * (u : Matrix (Fin n) (Fin n) (PSUF g))) *
            ((t⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) := by
          noncomm_ring
      _ = Unitary.antidiag n := by
          rw [huiso, htiI]

private theorem rckPSU_map_le_of_map_eq {U X : Type} [Group U] [Group X] {ψ : U →* X}
    (hker : ψ.ker ≤ Subgroup.center U) {J' : Subgroup U} (hperf : ⁅J', J'⁆ = J')
    {α : U →* U} (hmap : (J'.map α).map ψ = J'.map ψ) :
    J'.map α ≤ J' := by
  have hperf' : ⁅J'.map α, J'.map α⁆ = J'.map α := by
    rw [← Subgroup.map_commutator, hperf]
  rw [← hperf']
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  have hdec : ∀ x ∈ J'.map α, ∃ j ∈ J', ∃ z ∈ ψ.ker, x = j * z := by
    intro x hx
    have hx' : ψ x ∈ J'.map ψ := by
      rw [← hmap]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hψj⟩ := Subgroup.mem_map.mp hx'
    refine ⟨j, hj, j⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψj]
    group
  obtain ⟨ja, hja, za, hza, rfl⟩ := hdec a ha
  obtain ⟨jb, hjb, zb, hzb, rfl⟩ := hdec b hb
  have hcomm : ∀ x ∈ J', ∀ y ∈ ψ.ker, x * y = y * x :=
    fun x _ y hy => Subgroup.mem_center_iff.mp (hker hy) x
  rw [CFSG.GroupTheory.commutatorElement_mul_of_commute (A := J') (B := ψ.ker)
    hcomm hja hjb hza hzb]
  have hz : ⁅za, zb⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hker hza) zb).symm
  rw [hz, mul_one]
  exact hperf ▸ Subgroup.commutator_mem_commutator hja hjb


private lemma rckPSU_alpha {n g : ℕ} {X : Type} [Group X]
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X}
    {s : GL (Fin n) (PSUF g)} {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)} {b : X}
    {t t₁ : GL (Fin n) (PSUF g)}
    (ht : IsGLLift (PSUj n g) ψ t b)
    (hblock : ∀ y ∈ J', PSUj n g y ∈
      Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε))
    (hconj : ∀ x ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓
      glFixing (1 - ε), t * x * t⁻¹ = t₁ * x * t₁⁻¹)
    (hbK : b ∈ Subgroup.normalizer ((J'.map ψ : Subgroup X) : Set X))
    (ht₁GU : t₁ ∈ GUsub (PSUσ g) n) :
    ∃ α : ↥(Unitary.SU (PSUσ g) n) →* ↥(Unitary.SU (PSUσ g) n),
      (∀ u, PSUj n g (α u) = t₁ * PSUj n g u * t₁⁻¹) ∧
      (J'.map α).map ψ = J'.map ψ := by
  let α : ↥(Unitary.SU (PSUσ g) n) →* ↥(Unitary.SU (PSUσ g) n) :=
    { toFun := fun u => ⟨t₁ * PSUj n g u * t₁⁻¹, rckPSU_conj_mem_SU ht₁GU u.2⟩
      map_one' := by
        apply Subtype.ext
        change t₁ * PSUj n g 1 * t₁⁻¹ = 1
        rw [map_one]
        group
      map_mul' := fun u v => by
        apply Subtype.ext
        change t₁ * PSUj n g (u * v) * t₁⁻¹ =
          (t₁ * PSUj n g u * t₁⁻¹) * (t₁ * PSUj n g v * t₁⁻¹)
        rw [map_mul]
        group }
  have hψα : ∀ y ∈ J', ψ (α y) = b⁻¹ * ψ y * b := by
    intro y hy
    obtain ⟨u', hu'j, hu'ψ⟩ := ht y
    have hconjy : t * PSUj n g y * t⁻¹ = t₁ * PSUj n g y * t₁⁻¹ :=
      hconj (PSUj n g y) (hblock y hy)
    have hu'eq : u' = α y := by
      apply Subtype.ext
      show PSUj n g u' = PSUj n g (α y)
      rw [hu'j, hconjy]
      rfl
    rw [← hu'eq]
    exact hu'ψ.symm
  have hmap : (J'.map α).map ψ = J'.map ψ := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      rw [Subgroup.mem_map] at hw
      obtain ⟨y, hy, rfl⟩ := hw
      rw [hψα y hy]
      exact (Subgroup.mem_normalizer_iff''.mp hbK (ψ y)).mp
        (Subgroup.mem_map_of_mem ψ hy)
    · intro x hx
      rw [Subgroup.mem_map] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' : b * ψ y * b⁻¹ ∈ J'.map ψ :=
        (Subgroup.mem_normalizer_iff.mp hbK (ψ y)).mp (Subgroup.mem_map_of_mem ψ hy)
      rw [Subgroup.mem_map] at hy'
      obtain ⟨y', hy'mem, hy'eq⟩ := hy'
      refine ⟨α y', ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨y', hy'mem, rfl⟩
      · rw [hψα y' hy'mem, hy'eq]
        group
  exact ⟨α, fun _ => rfl, hmap⟩

private lemma rckPSU_normalizes_of_alpha {n g : ℕ}
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)} {t₁ : GL (Fin n) (PSUF g)}
    {α : ↥(Unitary.SU (PSUσ g) n) →* ↥(Unitary.SU (PSUσ g) n)}
    (hαapply : ∀ u, PSUj n g (α u) = t₁ * PSUj n g u * t₁⁻¹)
    (hαle : J'.map α ≤ J') :
    t₁ ∈ Subgroup.normalizer ((J'.map (PSUj n g) : Subgroup (GL (Fin n) (PSUF g))) :
      Set (GL (Fin n) (PSUF g))) := by
  let W : Subgroup (GL (Fin n) (PSUF g)) := J'.map (PSUj n g)
  have hWle : W.map (MulAut.conj t₁).toMonoidHom ≤ W := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact Subgroup.mem_map.mpr ⟨α z, hαle (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩), by
      simpa [MulAut.conj_apply] using hαapply z⟩
  have hWconj : W.map (MulAut.conj t₁).toMonoidHom = W := by
    have hcard : Nat.card ↥(W.map (MulAut.conj t₁).toMonoidHom) = Nat.card ↥W :=
      Subgroup.card_map_of_injective (f := (MulAut.conj t₁).toMonoidHom)
        (MulAut.conj t₁).injective
    exact Subgroup.eq_of_le_of_card_ge hWle (le_of_eq hcard.symm)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa [W] using hWconj

theorem rckLiftToBlock_PSU {n g : ℕ} {X : Type} [Group X]
    {ψ : ↥(Unitary.SU (PSUσ g) n) →* X} (hker : ψ.ker ≤ Subgroup.center _)
    {s : GL (Fin n) (PSUF g)} {ε : Matrix (Fin n) (Fin n) (PSUF g)}
    (hε : IsPrimAdjIdemIn (PSUσ g).toRingHom (Unitary.antidiag n)
      (Algebra.adjoin (PSUF g) (Units.val '' ({s} : Set (GL (Fin n) (PSUF g))))) ε)
    {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}
    (hJ'G : J' ≤ glBlockCentralizer (PSUj n g) {s} ε) (hperf : ⁅J', J'⁆ = J')
    {b : X} {t : GL (Fin n) (PSUF g)} (htU : t ∈ GUsub (PSUσ g) n)
    (ht : IsGLLift (PSUj n g) ψ t b) (hts : Commute t s)
    (hbK : b ∈ Subgroup.normalizer ((J'.map ψ : Subgroup X) : Set X)) :
    ∃ t₁ ∈ Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) ⊓
        GUsub (PSUσ g) n,
      t₁ ∈ Subgroup.normalizer ((J'.map (PSUj n g) : Subgroup (GL (Fin n) (PSUF g))) :
        Set (GL (Fin n) (PSUF g))) ∧
      ∀ y ∈ J', ∀ y' ∈ J', PSUj n g y' = t₁ * PSUj n g y * t₁⁻¹ → b⁻¹ * ψ y * b = ψ y' := by
  have hS : ∀ a ∈ ({s} : Set (GL (Fin n) (PSUF g))),
      ∀ a' ∈ ({s} : Set (GL (Fin n) (PSUF g))), Commute a a' := by
    intro a ha a' ha'
    rw [Set.mem_singleton_iff] at ha ha'
    rw [ha, ha']
  have hs' : ∀ a ∈ ({s} : Set (GL (Fin n) (PSUF g))), Commute t a := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact hts
  obtain ⟨htε, t₁, ht₁def, ht₁mem, _ht₁ord, ht₁conj⟩ :=
    rckGLBlock_restrict (S := ({s} : Set (GL (Fin n) (PSUF g)))) hS hε.1 hε.2.1 t hs'
  have ht₁GU : t₁ ∈ GUsub (PSUσ g) n := by
    rw [mem_GUsub_iff]
    exact rckGLBlock_restrict_isometry (σ := (PSUσ g).toRingHom) (G := Unitary.antidiag n)
      (PSUantidiag_isUnit_det n g) hε.2.2.2.1 hε.2.1 (mem_GUsub_iff.mp htU) htε ht₁def
  have hJ'block : ∀ y ∈ J', PSUj n g y ∈
      Subgroup.centralizer ({s} : Set (GL (Fin n) (PSUF g))) ⊓ glFixing (1 - ε) :=
    fun y hy => Subgroup.mem_comap.mp (hJ'G hy)
  obtain ⟨α, hαapply, hmap⟩ := rckPSU_alpha ht hJ'block ht₁conj hbK ht₁GU
  have hαle : J'.map α ≤ J' := rckPSU_map_le_of_map_eq hker hperf hmap
  have hnormal := rckPSU_normalizes_of_alpha hαapply hαle
  refine ⟨t₁, Subgroup.mem_inf.mpr ⟨ht₁mem, ht₁GU⟩, hnormal, ?_⟩
  intro y hy y' hy' hy'eq
  obtain ⟨u', hu'j, hu'ψ⟩ := ht y
  have hconj : t * PSUj n g y * t⁻¹ = t₁ * PSUj n g y * t₁⁻¹ :=
    ht₁conj (PSUj n g y) (hJ'block y hy)
  have hu'eq : u' = y' := by
    apply Subtype.ext
    show PSUj n g u' = PSUj n g y'
    rw [hu'j, hconj]
    exact hy'eq.symm
  rw [← hu'eq]
  exact hu'ψ

end CFSG.StandardType.RCKRP
