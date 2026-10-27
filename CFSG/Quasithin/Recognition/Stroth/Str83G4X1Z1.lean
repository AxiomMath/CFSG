module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4XNat2
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Shape5

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem str83G4_le_centralizerMod_z2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S)
    (hIQ2 : ⁅str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w, Q2 L1 L2 S⁆
      ≤ Z2 L1 L2 S) :
    L2 ⊔ S ≤ centralizerMod (Z2 L1 L2 S) ⊤
      (str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w) := by
  classical
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  have hfr : Str83G4Frame L1 L2 S a := ⟨hF, hB, ha, hSz, hL2, hZI⟩
  set I : Subgroup G := str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w with hIdef
  have hIQ2' : ⁅I, Q2 L1 L2 S⁆ ≤ Z2 L1 L2 S := by
    rw [hIdef]
    exact hIQ2
  have hIleX : I ≤ str83X L1 L2 S := by
    rw [hIdef]
    exact inf_le_left
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S :=
    (str83_caseI_basics hF hB ha hSz hL2 hZI).2.1
  have hNZ2P2 : P2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S)
  have hSP2 : S ≤ P2 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hL2P2 : L2 ⊔ S ≤ P2 L1 L2 S := sup_le le_sup_left hSP2
  have hQ1C : Q1 L1 L2 S ≤ centralizerMod (Z2 L1 L2 S) ⊤ I := by
    intro q hq
    refine mem_centralizerMod.mpr ⟨Subgroup.mem_top q,
      hNZ2P2 (hSP2 (str83G4_q1_le_s hfr hq)), ?_⟩
    intro y hy
    have h1 : ⁅y, q⁆ ∈ Z1 L1 L2 S :=
      str83G4_commutator_x_q1_le hfr (Subgroup.commutator_mem_commutator (hIleX hy) hq)
    have h2 : ⁅q, y⁆ ∈ Z1 L1 L2 S := by
      rw [← commutatorElement_inv]
      exact (Z1 L1 L2 S).inv_mem h1
    exact hZ1Z2 h2
  have hQ2C : Q2 L1 L2 S ≤ centralizerMod (Z2 L1 L2 S) ⊤ I := by
    intro q hq
    refine mem_centralizerMod.mpr ⟨Subgroup.mem_top q,
      hNZ2P2 ((pCoreOf_le 2 (P2 L1 L2 S)) hq), ?_⟩
    intro y hy
    have h1 : ⁅y, q⁆ ∈ Z2 L1 L2 S := Subgroup.commutator_le.mp hIQ2' y hy q hq
    have h2 : ⁅q, y⁆ ∈ Z2 L1 L2 S := by
      rw [← commutatorElement_inv]
      exact (Z2 L1 L2 S).inv_mem h1
    exact h2
  have hCS : S ≤ centralizerMod (Z2 L1 L2 S) ⊤ I := by
    have hSeq : S = Q1 L1 L2 S ⊔ Q2 L1 L2 S :=
      (str86_pCoreOf_sup_pCoreOf hF hB (Or.inl ⟨a, ha, hSz⟩) (by omega) hL2).symm
    calc S = Q1 L1 L2 S ⊔ Q2 L1 L2 S := hSeq
      _ ≤ centralizerMod (Z2 L1 L2 S) ⊤ I := sup_le hQ1C hQ2C
  have hwN : d.w ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) := hNZ2P2 (hL2P2 d.hwH2)
  have hCw : CFSG.conjugate S d.w ≤ centralizerMod (Z2 L1 L2 S) ⊤ I := by
    intro x hx
    have hxS : d.w * x * d.w⁻¹ ∈ S := (CFSG.mem_conjugate_iff S d.w x).mp hx
    have hsC : d.w * x * d.w⁻¹ ∈ centralizerMod (Z2 L1 L2 S) ⊤ I := hCS hxS
    have hsN : d.w * x * d.w⁻¹ ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
      (mem_centralizerMod.mp hsC).2.1
    refine mem_centralizerMod.mpr ⟨Subgroup.mem_top x, ?_, ?_⟩
    · have hxeq : x = d.w⁻¹ * (d.w * x * d.w⁻¹) * d.w := by group
      rw [hxeq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hwN) hsN) hwN
    · intro y hy
      have hw2P1 : d.w * d.w ∈ P1 L1 L2 S :=
        ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
          (str83G4_q2_le_s hfr (str83G4_w_mul_self_mem_q2 hfr d))
      have hw2N : d.w * d.w ∈ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
        le_normalizer_str83X L1 L2 S hw2P1
      have hyI : d.w * y * d.w⁻¹ ∈ I := by
        refine Subgroup.mem_inf.mpr ⟨(CFSG.mem_conjugate_iff (str83X L1 L2 S) d.w y).mp hy.2,
          ?_⟩
        refine (CFSG.mem_conjugate_iff (str83X L1 L2 S) d.w (d.w * y * d.w⁻¹)).mpr ?_
        rw [show d.w * (d.w * y * d.w⁻¹) * d.w⁻¹ =
          (d.w * d.w) * y * (d.w * d.w)⁻¹ by group]
        exact (Subgroup.mem_normalizer_iff.mp hw2N y).mp hy.1
      have hmain := (mem_centralizerMod.mp hsC).2.2 (d.w * y * d.w⁻¹) hyI
      have heq : x * y * x⁻¹ * y⁻¹ = d.w⁻¹ * ((d.w * x * d.w⁻¹) * (d.w * y * d.w⁻¹) *
        (d.w * x * d.w⁻¹)⁻¹ * (d.w * y * d.w⁻¹)⁻¹) * d.w := by group
      rw [heq]
      exact (Subgroup.mem_normalizer_iff''.mp hwN _).mp hmain
  calc L2 ⊔ S = S ⊔ CFSG.conjugate S d.w := d.hwTop.symm
    _ ≤ centralizerMod (Z2 L1 L2 S) ⊤ I := sup_le hCS hCw

theorem str83G4_commutator_mem_z2_of_mem_x_inf_conjugate
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ∀ g ∈ L2 ⊔ S, ∀ y ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w,
      g * y * g⁻¹ * y⁻¹ ∈ Z2 L1 L2 S :=
  fun g hg y hy => (mem_centralizerMod.mp (str83G4_le_centralizerMod_z2 hfr d
    (str83G4_commutator_x_inf_conjugate_x_q2_le hfr d hX hB) hg)).2.2 y hy

private theorem str83G4_commutator_eq_one_of_mem_x1_of_mem_q2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S)
    (hIQ2 : ⁅str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w, Q2 L1 L2 S⁆
      ≤ Z2 L1 L2 S)
    (hX1I : str83X1 L1 L2 S ≤
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hZ2step : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S))
    {x : G} (hx : x ∈ str83X1 L1 L2 S) :
    ∀ u ∈ Q2 L1 L2 S, x * u = u * x := by
  classical
  have hxI : x ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w := hX1I hx
  have hZ2CQ2 : Z2 L1 L2 S ≤ Subgroup.centralizer (Q2 L1 L2 S : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp
      (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hq) z hz).symm
  have hZ2ab : ∀ z ∈ Z2 L1 L2 S, ∀ w ∈ Z2 L1 L2 S, z * w = w * z :=
    fun z hz w hw => A4.mul_comm_of_mem_omegaOneCenterOf hz hw
  let φ : ↥(Q2 L1 L2 S) →* G :=
    { toFun := fun u => ⁅x, (u : G)⁆
      map_one' := by
        show ⁅x, ((1 : ↥(Q2 L1 L2 S)) : G)⁆ = 1
        rw [Subgroup.coe_one, commutatorElement_one_right]
      map_mul' := fun u v => by
        show ⁅x, ((u * v : ↥(Q2 L1 L2 S)) : G)⁆ = ⁅x, (u : G)⁆ * ⁅x, (v : G)⁆
        rw [Subgroup.coe_mul, commutatorElement_mul_right_eq_mul_conj]
        have hmem : ⁅x, (v : G)⁆ ∈ Z2 L1 L2 S :=
          Subgroup.commutator_le.mp hIQ2 x hxI (v : G) v.2
        have hcent : (u : G) * ⁅x, (v : G)⁆ = ⁅x, (v : G)⁆ * (u : G) :=
          Subgroup.mem_centralizer_iff.mp (hZ2CQ2 hmem) (u : G) u.2
        calc ⁅x, (u : G)⁆ * (u : G) * ⁅x, (v : G)⁆ * (u : G)⁻¹
            = ⁅x, (u : G)⁆ * ((u : G) * ⁅x, (v : G)⁆ * (u : G)⁻¹) := by group
          _ = ⁅x, (u : G)⁆ * ⁅x, (v : G)⁆ := by rw [hcent]; group }
  have hφZ2 : φ.range ≤ Z2 L1 L2 S := by
    rintro e ⟨u, rfl⟩
    exact Subgroup.commutator_le.mp hIQ2 x hxI (u : G) u.2
  have hφZ1 : φ.range ≤ Z1 L1 L2 S := by
    rintro e ⟨u, rfl⟩
    have hu : (u : G) ∈ L1 ⊔ S :=
      (le_sup_right : S ≤ L1 ⊔ S) (str83G4_q2_le_s hfr u.2)
    exact (mem_str83X1.mp hx).2.2 (u : G) hu
  have hnorm : IsNormalIn (L2 ⊔ S) (Z2 L1 L2 S) φ.range := by
    refine ⟨hφZ2, ?_⟩
    intro g hg e he
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp he
    have hgP2 : g ∈ P2 L1 L2 S :=
      (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)) hg
    set v : G := g * (u : G) * g⁻¹ with hvdef
    have hvQ2 : v ∈ Q2 L1 L2 S := by
      rw [hvdef]
      exact (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 (P2 L1 L2 S) hgP2) (u : G)).mp u.2
    refine MonoidHom.mem_range.mpr ⟨⟨v, hvQ2⟩, ?_⟩
    symm
    set z : G := g * x * g⁻¹ * x⁻¹ with hzdef
    have hzx : g * x * g⁻¹ = z * x := by rw [hzdef]; group
    have hzZ2 : z ∈ Z2 L1 L2 S :=
      (mem_centralizerMod.mp (str83G4_le_centralizerMod_z2 hfr d hIQ2 hg)).2.2 x hxI
    have hzv : ⁅z, v⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (hZ2CQ2 hzZ2) v hvQ2).symm
    have hxvZ2 : ⁅x, v⁆ ∈ Z2 L1 L2 S :=
      Subgroup.commutator_le.mp hIQ2 x hxI v hvQ2
    have hzconj : z * ⁅x, v⁆ * z⁻¹ = ⁅x, v⁆ := by
      rw [hZ2ab z hzZ2 ⁅x, v⁆ hxvZ2]
      group
    calc g * ⁅x, (u : G)⁆ * g⁻¹ = ⁅g * x * g⁻¹, v⁆ := by
          rw [conjugate_commutatorElement, hvdef]
      _ = ⁅z * x, v⁆ := by rw [hzx]
      _ = z * ⁅x, v⁆ * z⁻¹ * ⁅z, v⁆ := by rw [commutatorElement_mul_left_eq_conj_mul]
      _ = ⁅x, v⁆ := by rw [hzv, mul_one, hzconj]
  rcases hZ2step.2.2.2 φ.range hnorm bot_le hφZ2 with hbot | htop
  · intro u hu
    have hmem : φ ⟨u, hu⟩ ∈ φ.range := MonoidHom.mem_range.mpr ⟨⟨u, hu⟩, rfl⟩
    rw [hbot] at hmem
    have hone : ⁅x, u⁆ = 1 := Subgroup.mem_bot.mp hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hone
  · exfalso
    have hZ2le : Z2 L1 L2 S ≤ Z1 L1 L2 S := htop ▸ hφZ1
    have hSZ1 : S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
      (le_sup_right : S ≤ L1 ⊔ S).trans (str83G4_sup_le_centralizer_z1 hfr)
    have hZ1bot : Z1 L1 L2 S = ⊥ := by
      have hcomm : ⁅Z2 L1 L2 S, S⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        exact (Subgroup.mem_centralizer_iff.mp (hSZ1 hs) z (hZ2le hz)).symm
      rw [← str83G4_commutator_z2_s hfr]
      exact hcomm
    exact not_le_of_gt hZ2step.2.2.1 (hZ1bot ▸ hZ2le)

theorem str83G4_x1_eq_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    str83X1 L1 L2 S = Z1 L1 L2 S := by
  refine le_antisymm ?_ (str83G4_z1_le_x1 hfr)
  intro x hx
  have hxcent := str83G4_commutator_eq_one_of_mem_x1_of_mem_q2 hfr d
    (str83G4_commutator_x_inf_conjugate_x_q2_le hfr d hX hB)
    (str83G4_x1_le_x_inf_conjugate_x hfr d hX hB) (str83G4_isChiefStep_z2 hfr d hX hB) hx
  have hxX : x ∈ str83X L1 L2 S := str83G4_x1_le_x L1 L2 S hx
  have hxQ2 : x ∈ Q2 L1 L2 S := str83G4_x_le_q2 hfr hX hxX
  have hx2 : x ^ 2 = 1 := (B6.isElemAbelian_iff.mp hX).2 x hxX
  have hxZ2 : x ∈ Z2 L1 L2 S := by
    refine Subgroup.subset_closure ⟨?_, hx2⟩
    exact Subgroup.mem_inf.mpr ⟨hxQ2,
      Subgroup.mem_centralizer_iff.mpr fun y hy => (hxcent y hy).symm⟩
  have hmem : x ∈ Z2 L1 L2 S ⊓ str83X1 L1 L2 S := ⟨hxZ2, hx⟩
  rwa [str83G4_z2_inf_x1 hfr d hX hB] at hmem

theorem str83G4_isChiefStep_x_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) (str83X L1 L2 S) := by
  have h := str83G4_isChiefStep_x1_x hfr d hX hB
  rwa [str83G4_x1_eq_z1 hfr d hX hB] at h

theorem str83G4_not_twoResidual_le_centralizerMod_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ¬ twoResidual (L1 ⊔ S) ≤
      centralizerMod (Z1 L1 L2 S) (L1 ⊔ S) (str83X L1 L2 S) := by
  rw [← str83G4_x1_eq_z1 hfr d hX hB]
  exact str83G4_not_twoResidual_le_centralizerMod_x1 hfr d hX hB

theorem str83G4_isSzNaturalSection_x_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    IsSzNaturalSection (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) a := by
  rw [← str83G4_x1_eq_z1 hfr d hX hB]
  exact str83G4_isSzNaturalSection_x_x1 hfr d hX hB

theorem str83G4_relIndex_z1_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    (Z1 L1 L2 S).relIndex (str83X L1 L2 S) = (2 ^ (2 * a + 1)) ^ 4 :=
  relIndex_eq_of_isSzNaturalSection
    (str83G4_isSzNaturalSection_x_z1 hfr d hX hB)

end CFSG.Quasithin.Stroth

end
