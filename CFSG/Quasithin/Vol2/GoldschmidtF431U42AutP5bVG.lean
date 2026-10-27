module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bVA
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Tr
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2Tr

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}

theorem AutIso.pCoreOf_M₂
    (iso : AutIso M₁ M₂) : pCoreOf 2 M₂ = iso.imgG VA := by
  have hP : (CFSG.Open.pCore 2 ↥P2h).map P2h.subtype = VA := pCoreOf_P2h_eq
  have hM : (CFSG.Open.pCore 2 ↥P2h).map iso.phi2.toMonoidHom = CFSG.Open.pCore 2 ↥M₂ :=
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 iso.phi2
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
    rw [← hM] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hyV : (y : Ah) ∈ VA := by
      rw [← hP]
      exact Subgroup.mem_map_of_mem _ hy
    refine iso.mem_imgG.2 ⟨⟨(y : Ah), VA_le_Bh hyV⟩, hyV, ?_⟩
    have e : Subgroup.inclusion Bh_le_P2h ⟨(y : Ah), VA_le_Bh hyV⟩ = y := Subtype.ext rfl
    have h := iso.toG2_inclusion ⟨(y : Ah), VA_le_Bh hyV⟩
    rw [e] at h
    exact h.symm
  · intro hg
    obtain ⟨b, hbV, rfl⟩ := iso.mem_imgG.1 hg
    set y : ↥P2h := Subgroup.inclusion Bh_le_P2h b with hy
    have hyP : y ∈ CFSG.Open.pCore 2 ↥P2h := by
      have : (y : Ah) ∈ (CFSG.Open.pCore 2 ↥P2h).map P2h.subtype := by rw [hP]; exact hbV
      obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.1 this
      have : y' = y := Subtype.ext hyy'
      rwa [this] at hy'
    have hx : iso.phi2 y ∈ CFSG.Open.pCore 2 ↥M₂ := by
      rw [← hM]
      exact Subgroup.mem_map_of_mem _ hyP
    refine Subgroup.mem_map.2 ⟨iso.phi2 y, hx, ?_⟩
    exact iso.toG2_inclusion b

theorem AutIso.Vg_comm
    (iso : AutIso M₁ M₂) {a b : G} (ha : a ∈ iso.imgG VA) (hb : b ∈ iso.imgG VA) :
    a * b = b * a := by
  obtain ⟨a', ha', rfl⟩ := iso.mem_imgG.1 ha
  obtain ⟨b', hb', rfl⟩ := iso.mem_imgG.1 hb
  rw [← AutIso.toG_mul, ← AutIso.toG_mul]
  congr 1
  exact Subtype.ext (VA_comm ha' hb')

theorem AutIso.Vg_sq
    (iso : AutIso M₁ M₂) {a : G} (ha : a ∈ iso.imgG VA) : a * a = 1 := by
  obtain ⟨a', ha', rfl⟩ := iso.mem_imgG.1 ha
  rw [← AutIso.toG_mul]
  have : a' * a' = 1 := Subtype.ext (VA_sq ha')
  rw [this]
  exact iso.toG_one

theorem AutIso.centerOf_pCoreOf_M₂
    (iso : AutIso M₁ M₂) : centerOf (pCoreOf 2 M₂) = iso.imgG VA := by
  rw [iso.pCoreOf_M₂]
  ext g
  constructor
  · intro hg
    exact hg.1
  · intro hg
    refine ⟨hg, Subgroup.mem_centralizer_iff.2 fun h hh => iso.Vg_comm hh hg⟩

theorem AutCtx.normalizer_Vg
    [Finite G] {z : G} (c : AutCtx G M₁ M₂ z) :
    Subgroup.normalizer ((c.iso.imgG VA : Subgroup G) : Set G) = M₂ := by
  rw [← c.iso.centerOf_pCoreOf_M₂]
  exact c.N2

end CFSG.Quasithin.H13.F431.U42Aut
