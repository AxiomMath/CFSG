module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Steps1c
public import CFSG.Quasithin.Vol2.Ch8Sec2L822KzBranch
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem map_normal_two_le_pCore_cov {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (N : Subgroup X) [N.Normal] (hN : IsPGroup 2 N) :
    N.map f ≤ CFSG.pCore 2 Y :=
  CFSG.LieType.BorelTits.le_pCore 2 (Subgroup.Normal.map ‹N.Normal› f hf) (hN.map f)

theorem pCore_eq_bot_of_mulEquiv_cov {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.pCore 2 A = ⊥) : CFSG.pCore 2 B = ⊥ := by
  have hle : (CFSG.pCore 2 B).map e.symm.toMonoidHom ≤ CFSG.pCore 2 A := by
    haveI : (CFSG.pCore 2 B).Normal := CFSG.pCore_normal
    exact map_normal_two_le_pCore_cov e.symm.toMonoidHom e.symm.surjective (CFSG.pCore 2 B)
      (CFSG.pCore_isPGroup (p := 2) (G := B))
  rw [h] at hle
  rw [eq_bot_iff]
  intro x hx
  have hx' : e.symm x ∈ (CFSG.pCore 2 B).map e.symm.toMonoidHom := Subgroup.mem_map_of_mem _ hx
  have := Subgroup.mem_bot.mp (hle hx')
  rw [Subgroup.mem_bot]
  exact e.symm.injective (by simpa using this)


theorem cov_Lbar_ne_Kbar {G : Type} [Group G] [Finite G] {Gz T H M Lz Kz : Subgroup G} {y : G}
    (hT : IsSylowTwoOf T Gz) (hTM : T ≤ M) (hHGz : H ≤ Gz) (hLzG : Lz ≤ Gz)
    (hLzq : IsHat (↥Lz ⧸ CFSG.pCore 2 ↥Lz) (alternatingGroup (Fin 6)))
    (hLK : Lz ≤ Kz) (hKz : Kz ∈ cComp Gz) (hKn : Gz ≤ Subgroup.normalizer (Kz : Set G))
    (hyM : y ∈ M) (hyL : y ∈ Lz) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hcomm : ∀ l ∈ Lz, y⁻¹ * l⁻¹ * y * l ∈ pCoreOf 2 Lz)
    (heq : modO2Image Gz Lz = modO2Image Gz Kz) :
    ∀ h ∈ H, h * y * h⁻¹ ∈ M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥Gz →* ↥Gz ⧸ CFSG.pCore 2 ↥Gz := QuotientGroup.mk' (CFSG.pCore 2 ↥Gz) with hπ
  have hKG : Kz ≤ Gz := le_of_mem_cComp hKz
  have hyG : y ∈ Gz := hLzG hyL
  set Kb := modO2Image Gz Kz with hKb
  have hKbn : Kb.Normal := by
    have : (Kz.subgroupOf Gz).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mpr hKn
    exact Subgroup.Normal.map this π (QuotientGroup.mk'_surjective _)
  have hO2 : CFSG.pCore 2 ↥Kb = ⊥ := by
    obtain ⟨e⟩ := modO2_mulEquiv hKz
    exact pCore_eq_bot_of_mulEquiv_cov e CFSG.Quasithin.B6.pCore_quotient_pCore
  have hmemKb : ∀ l (hl : l ∈ Lz), π ⟨l, hLzG hl⟩ ∈ Kb := by
    intro l hl
    rw [← heq]
    exact CFSG.Quasithin.P134.mk_mem_modO2Image hl (hLzG hl)
  let f : ↥Lz →* ↥Kb :=
    (π.comp (Subgroup.inclusion hLzG)).codRestrict Kb (fun x => hmemKb x x.2)
  have hfπ : ∀ x : ↥Lz, ((f x : ↥Kb) : ↥Gz ⧸ CFSG.pCore 2 ↥Gz) = π ⟨x, hLzG x.2⟩ := fun x => rfl
  have hf : Function.Surjective f := by
    intro k
    have hk : (k : ↥Gz ⧸ CFSG.pCore 2 ↥Gz) ∈ modO2Image Gz Lz := by
      rw [heq]
      exact k.2
    obtain ⟨l, hl, hlG, hlk⟩ := kzMemModO2Image_kz3.mp hk
    exact ⟨⟨l, hl⟩, Subtype.ext hlk⟩
  have hkerf : f.ker = CFSG.pCore 2 ↥Lz := by
    apply le_antisymm
    · intro x hx
      have h1 : π ⟨x, hLzG x.2⟩ = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        simpa [hfπ] using this
      have h2 : (⟨x, hLzG x.2⟩ : ↥Gz) ∈ CFSG.pCore 2 ↥Gz := (QuotientGroup.eq_one_iff _).mp h1
      exact kzMemPCoreOfMemPCoreOf_kz3 hLzG x ((CFSG.Quasithin.P134.mem_pCoreOf_iff (hLzG x.2)).mpr h2)
    · intro x hx
      haveI : (CFSG.pCore 2 ↥Lz).Normal := CFSG.pCore_normal
      have h1 := map_normal_two_le_pCore_cov f hf (CFSG.pCore 2 ↥Lz) (CFSG.pCore_isPGroup (p := 2) (G := ↥Lz))
      have h2 : f x ∈ CFSG.pCore 2 ↥Kb := h1 (Subgroup.mem_map_of_mem f hx)
      rw [hO2, Subgroup.mem_bot] at h2
      exact h2
  haveI hNL : (CFSG.pCore 2 ↥Lz).Normal := CFSG.pCore_normal
  have eKb : (↥Lz ⧸ CFSG.pCore 2 ↥Lz) ≃* ↥Kb :=
    (QuotientGroup.quotientMulEquivOfEq hkerf.symm).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hZ3 : Nat.card ↥(Subgroup.center ↥Kb) = 3 := by
    have h1 := Subgroup.map_center_eq eKb
    rw [← h1, Subgroup.card_map_of_injective eKb.injective]
    exact hLzq.2.1
  set ybar : ↥Kb := f ⟨y, hyL⟩ with hybar
  have hybarc : ybar ∈ Subgroup.center ↥Kb := by
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨l, rfl⟩ := hf k
    have hc : (⟨y, hyL⟩ : ↥Lz)⁻¹ * (l : ↥Lz)⁻¹ * ⟨y, hyL⟩ * l ∈ CFSG.pCore 2 ↥Lz := by
      have h1 := hcomm l l.2
      have e : (⟨y, hyL⟩ : ↥Lz)⁻¹ * (l : ↥Lz)⁻¹ * ⟨y, hyL⟩ * l =
          ⟨y⁻¹ * (l : G)⁻¹ * y * l, Lz.mul_mem (Lz.mul_mem (Lz.mul_mem (Lz.inv_mem hyL)
            (Lz.inv_mem l.2)) hyL) l.2⟩ := Subtype.ext (by simp)
      rw [e]
      exact (mem_pCore_iff_kz2 _).mpr h1
    have h3 : f ((⟨y, hyL⟩ : ↥Lz)⁻¹ * (l : ↥Lz)⁻¹ * ⟨y, hyL⟩ * l) = 1 := by
      rw [← MonoidHom.mem_ker, hkerf]
      exact hc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    have h4 : ybar⁻¹ * (f l)⁻¹ * ybar * f l = 1 := h3
    calc f l * ybar = (f l * ybar) * (ybar⁻¹ * (f l)⁻¹ * ybar * f l) := by rw [h4, mul_one]
      _ = ybar * f l := by group
  have hybar1 : ybar ≠ 1 := by
    intro h1
    have h2 : (⟨y, hyL⟩ : ↥Lz) ∈ f.ker := MonoidHom.mem_ker.mpr h1
    rw [hkerf] at h2
    have := kzEqOnePowThreeMem_kz3 (CFSG.pCore_isPGroup (p := 2) (G := ↥Lz)) (g := ⟨y, hyL⟩)
      (Subtype.ext (by simpa using hy3)) h2
    exact hy1 (congrArg Subtype.val this)
  have hybar3 : ybar ^ 3 = 1 := by
    rw [hybar, ← map_pow]
    have : (⟨y, hyL⟩ : ↥Lz) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hord : orderOf ybar = 3 := orderOf_eq_prime hybar3 hybar1
  have hzp : Subgroup.zpowers ybar = Subgroup.center ↥Kb :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hybarc) (by rw [Nat.card_zpowers, hord, hZ3])
  have hZn : ∀ g : ↥Gz ⧸ CFSG.pCore 2 ↥Gz, ∀ z : ↥Kb, z ∈ Subgroup.center ↥Kb →
      ∃ z' : ↥Kb, z' ∈ Subgroup.center ↥Kb ∧
        (z' : ↥Gz ⧸ CFSG.pCore 2 ↥Gz) = g * (z : ↥Gz ⧸ CFSG.pCore 2 ↥Gz) * g⁻¹ := by
    intro g z hz
    have hmem : g * (z : ↥Gz ⧸ CFSG.pCore 2 ↥Gz) * g⁻¹ ∈ Kb := hKbn.conj_mem _ z.2 g
    refine ⟨⟨g * z * g⁻¹, hmem⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have hk' : g⁻¹ * (k : ↥Gz ⧸ CFSG.pCore 2 ↥Gz) * g ∈ Kb := by
      have := hKbn.conj_mem _ k.2 g⁻¹
      simpa using this
    have hcomm' := (Subgroup.mem_center_iff.mp hz) ⟨g⁻¹ * k * g, hk'⟩
    have hc2 := congrArg Subtype.val hcomm'
    simp only [Subgroup.coe_mul] at hc2 ⊢
    calc (k : ↥Gz ⧸ CFSG.pCore 2 ↥Gz) * (g * z * g⁻¹)
        = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc2]
      _ = (g * z * g⁻¹) * k := by group
  have hOT : pCoreOf 2 Gz ≤ T :=
    pCoreOf_le_of_sylow_kz2 hT le_rfl (hT.1.trans Subgroup.le_normalizer)
  intro h hh
  have hhG : h ∈ Gz := hHGz hh
  have hmemG : h * y * h⁻¹ ∈ Gz := Gz.mul_mem (Gz.mul_mem hhG hyG) (Gz.inv_mem hhG)
  obtain ⟨z', hz'c, hz'⟩ := hZn (π ⟨h, hhG⟩) ybar hybarc
  rw [← hzp] at hz'c
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz'c
  have hyj : y ^ j ∈ Gz := zpow_mem hyG j
  have hπeq : π ⟨h * y * h⁻¹, hmemG⟩ = π ⟨y ^ j, hyj⟩ := by
    have h1 : π ⟨h * y * h⁻¹, hmemG⟩ = π ⟨h, hhG⟩ * π ⟨y, hyG⟩ * (π ⟨h, hhG⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have h2 : π ⟨y ^ j, hyj⟩ = (π ⟨y, hyG⟩) ^ j := by
      rw [← map_zpow]
      rfl
    rw [h1, h2]
    have h3 : (z' : ↥Gz ⧸ CFSG.pCore 2 ↥Gz) = (ybar : ↥Gz ⧸ CFSG.pCore 2 ↥Gz) ^ j := by
      rw [← hj]
      rfl
    have h4 : π ⟨h, hhG⟩ * π ⟨y, hyG⟩ * (π ⟨h, hhG⟩)⁻¹ = (z' : ↥Gz ⧸ CFSG.pCore 2 ↥Gz) := hz'.symm
    rw [h4, h3]
    rfl
  have hmem2 : (⟨y ^ j, hyj⟩ : ↥Gz)⁻¹ * ⟨h * y * h⁻¹, hmemG⟩ ∈ CFSG.pCore 2 ↥Gz := QuotientGroup.eq.mp hπeq.symm
  have hmem3 : (y ^ j)⁻¹ * (h * y * h⁻¹) ∈ pCoreOf 2 Gz :=
    (CFSG.Quasithin.P134.mem_pCoreOf_iff (Gz.mul_mem (Gz.inv_mem hyj) hmemG)).mpr hmem2
  have hyjM : y ^ j ∈ M := zpow_mem hyM j
  have : h * y * h⁻¹ = y ^ j * ((y ^ j)⁻¹ * (h * y * h⁻¹)) := by group
  rw [this]
  exact M.mul_mem hyjM (hTM (hOT hmem3))

end CFSG.Quasithin.H13
