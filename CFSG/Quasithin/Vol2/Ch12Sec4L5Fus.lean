module

public import CFSG.Quasithin.Vol2.Ch12Sec4L5Mbar
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem16Orbit
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {z : G}

namespace Cx5Facts

theorem exists_conj_eq_of_mem
    (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight) (h12210 : Stmt12_2_10)
    (h1229 : Stmt12_2_9) (hpre : Pre1242) (h42 : AsB42) (hcx : Cx1242 G T L V)
    (hf : Cx5Facts G T L V z)
    (h5 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))
    {g : G} (hg : g * z * g⁻¹ ∈ V) : ∃ l ∈ L, l * z * l⁻¹ = g * z * g⁻¹ := by
  have := hf.comm
  have hyp := hcx.hyp
  have hW2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)
  have hNV : autOn (Subgroup.normalizer (V : Set G)) V = autOn L V :=
    le_antisymm ((autOn_mono (hf.normalizer_le h1222 h323 hcx)).trans
      (hf.mbarV_eq h1222 h3228 h12210 h1229 hpre h42 hcx h5).le) (autOn_mono hf.normalizes)
  obtain ⟨hlen, hsep⟩ := Orbit.orbitL52Ten ↥V hW2 hf.card (autOn L V) (hf.lbar_equiv h5)
    hf.irr_lbar
  have hcard : ∀ (w : G) (hw : w ∈ V), Nat.card (Orbit.orbitIn (autOn L V) ⟨w, hw⟩) *
      Nat.card ↥(Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer ({w} : Set G)) =
        Nat.card ↥(Subgroup.normalizer (V : Set G)) := fun w hw => by
    have h1 := Lem16.card_orbitIn_mul_card_centralizer le_rfl (⟨w, hw⟩ : ↥V)
    rwa [hNV] at h1
  have hlen' : ∀ (w : G) (hw : w ∈ V), (⟨w, hw⟩ : ↥V) ≠ 1 →
      Nat.card (Orbit.orbitIn (autOn L V) ⟨w, hw⟩) = 155 ∨
        Nat.card (Orbit.orbitIn (autOn L V) ⟨w, hw⟩) = 868 := fun w hw hw1 => by
    rcases List.mem_cons.1 (hlen ⟨w, hw⟩ hw1) with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.1 h)
  have hz1 : (⟨z, hf.mem.1⟩ : ↥V) ≠ 1 := fun h => hf.ne_one (congrArg Subtype.val h)
  have hCz : Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer ({z} : Set G) =
      Subgroup.centralizer ({z} : Set G) :=
    inf_eq_right.2 (hf.centralizer_le h1222 h323 hcx)
  have hz := hcard z hf.mem.1
  rw [hCz] at hz
  have hZT : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
    ((Subgroup.closure_le _).mpr fun _ hx => hx.1).trans inf_le_right
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hZT hf.mem.2) t ht)
  have h155 : Nat.card (Orbit.orbitIn (autOn L V) ⟨z, hf.mem.1⟩) = 155 := by
    rcases hlen' z hf.mem.1 hz1 with h | h
    · exact h
    exfalso
    rw [h] at hz
    have h1 : 868 * Nat.card T ∣ Nat.card G := by
      have h2 : Nat.card T ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set G)) :=
        Subgroup.card_dvd_of_le hTz
      have h3 : Nat.card ↥(Subgroup.normalizer (V : Set G)) ∣ Nat.card G :=
        Subgroup.card_subgroup_dvd_card _
      rw [← hz] at h3
      exact (Nat.mul_dvd_mul_left 868 h2).trans h3
    rw [← T.card_mul_index, mul_comm 868] at h1
    have h2 : 868 ∣ T.index := Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h1
    exact hyp.sylow.2 ((show (2 : ℕ) ∣ 868 by norm_num).trans h2)
  have hy1 : (⟨g * z * g⁻¹, hg⟩ : ↥V) ≠ 1 := fun h => hf.ne_one (by
    have h1 : g * z * g⁻¹ = 1 := congrArg Subtype.val h
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  have hCy : Nat.card ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({z} : Set G)) := by
    rw [centralizer_singleton_eq_conjugate (show g⁻¹⁻¹ * z * g⁻¹ = g * z * g⁻¹ by rw [inv_inv]),
      card_conjugate_eq]
  have h155y : Nat.card (Orbit.orbitIn (autOn L V) ⟨g * z * g⁻¹, hg⟩) = 155 := by
    rcases hlen' _ hg hy1 with h | h
    · exact h
    exfalso
    have hy := hcard _ hg
    rw [h] at hy
    have hz' := hcard z hf.mem.1
    rw [h155, hCz] at hz'
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (inf_le_right :
      Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer ({g * z * g⁻¹} : Set G) ≤
        Subgroup.centralizer ({g * z * g⁻¹} : Set G))
    rw [hCy] at hk
    have hpos : 0 < Nat.card ↥(Subgroup.normalizer (V : Set G) ⊓
        Subgroup.centralizer ({g * z * g⁻¹} : Set G)) := Nat.card_pos
    generalize Nat.card ↥(Subgroup.normalizer (V : Set G) ⊓
      Subgroup.centralizer ({g * z * g⁻¹} : Set G)) = d at hy hk hpos
    have h1 : d * 868 = d * (155 * k) := by
      rw [mul_comm d 868, hy, ← hz', hk]
      ring
    have h2 := Nat.eq_of_mul_eq_mul_left hpos h1
    omega
  obtain ⟨a, ha, hav⟩ := hsep _ _ hz1 hy1 (h155.trans h155y.symm)
  obtain ⟨l, hl, hle⟩ := exists_eq_conj_of_mem_autOn hf.normalizes ha
  refine ⟨l, hl, ?_⟩
  have h1 := hle ⟨z, hf.mem.1⟩
  rw [hav] at h1
  exact h1.symm

theorem commutator_eq_bot_of_mem
    (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight) (h12210 : Stmt12_2_10)
    (h1229 : Stmt12_2_9) (hpre : Pre1242) (h42 : AsB42) (hcx : Cx1242 G T L V)
    (hf : Cx5Facts G T L V z)
    (h5 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))
    {g : G} (hz : z ∈ CFSG.conjugate V g) : ⁅V, CFSG.conjugate V g⁆ = ⊥ := by
  have hy : g * z * g⁻¹ ∈ V := mem_conjugate_iff_mul_mem.1 hz
  obtain ⟨l, hl, hlz⟩ :=
    hf.exists_conj_eq_of_mem h1222 h323 h3228 h12210 h1229 hpre h42 hcx h5 hy
  have hc : l⁻¹ * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc l⁻¹ * g * z = l⁻¹ * (g * z * g⁻¹) * g := by group
      _ = l⁻¹ * (l * z * l⁻¹) * g := by rw [hlz]
      _ = z * (l⁻¹ * g) := by group
  have hgN : g ∈ Subgroup.normalizer (V : Set G) := by
    have h1 := (Subgroup.normalizer (V : Set G)).mul_mem (hf.normalizes hl)
      (hf.centralizer_le h1222 h323 hcx hc)
    rwa [mul_inv_cancel_left] at h1
  rw [conjugate_eq_of_mem_normalizer' hgN]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hf.le_centralizer

end Cx5Facts

end CFSG.Quasithin.H13
