module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertA5
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveDefs

public section

namespace CFSG.Quasithin.H13.FiveNorm

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L.PermLat Equiv

theorem noFiveOver_alt_of_cert {n : ℕ} (c : LatCert (Perm (Fin n)))
    (hc : c.check RN.enc = true)
    (hM : Subgroup.closure {g | g ∈ c.mGens} = alternatingGroup (Fin n))
    (hDA : Subgroup.closure {g | g ∈ c.tGens} ≤ alternatingGroup (Fin n))
    (hDs : IsSylowTwoOf ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
      (alternatingGroup (Fin n))) ⊤)
    {k : ℕ} (hDk : Nat.card ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf
      (alternatingGroup (Fin n))) = 2 ^ k)
    (hsizes : 5 * 2 ^ k ∉ c.sizes) : NoFiveOver ↥(alternatingGroup (Fin n)) := by
  classical
  intro S H hS hSH hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := isSylowTwoOf_top_index hS
  obtain ⟨h3, h4⟩ := isSylowTwoOf_top_index hDs
  have hSk : Nat.card S = 2 ^ k := by
    rw [← hDk]
    have e1 := Sylow.card_eq_multiplicity (h1.toSylow h2)
    have e2 := Sylow.card_eq_multiplicity (h3.toSylow h4)
    exact e1.trans e2.symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin n)) (h1.toSylow h2)
    (h3.toSylow h4)
  have hDH : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf (alternatingGroup (Fin n)) ≤
      H.map (MulAut.conj g).toMonoidHom := by
    intro x hx
    have hx' : x ∈ ((g • h1.toSylow h2 : Sylow 2 (alternatingGroup (Fin n))) :
        Subgroup (alternatingGroup (Fin n))) := by
      rw [hg]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    exact ⟨y, hSH hy, rfl⟩
  have hHc : Nat.card (H.map (MulAut.conj g).toMonoidHom) = 5 * 2 ^ k := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard, hSk]
  have hTY : Subgroup.closure {g | g ∈ c.tGens} ≤
      (H.map (MulAut.conj g).toMonoidHom).map (alternatingGroup (Fin n)).subtype := by
    intro t ht
    exact ⟨⟨t, hDA ht⟩, hDH (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hYM : (H.map (MulAut.conj g).toMonoidHom).map (alternatingGroup (Fin n)).subtype ≤
      Subgroup.closure {g | g ∈ c.mGens} := by
    rw [hM]
    exact Subgroup.map_subtype_le _
  obtain ⟨L, hL, hYL⟩ := c.overgroups (rawIsEnc n) hc _ hTY hYM
  have hmem := c.card_member (rawIsEnc n) (c.closedOK_of_check hc) (c.sizesOK_of_check hc) L hL
  rw [← hYL, Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective,
    hHc] at hmem
  exact hsizes hmem

theorem noFiveOver_alt5 :
    NoFiveOver ↥(alternatingGroup (Fin 5)) := by
  have hD := CFSG.QuasithinUnique.Bridge.Over.CertA5.isSylow_D
  exact noFiveOver_alt_of_cert CFSG.QuasithinUnique.Bridge.Over.CertA5.cert
    CFSG.QuasithinUnique.Bridge.Over.CertA5.cert_check
    CFSG.QuasithinUnique.Bridge.Over.CertA5.closure_mGens
    CFSG.QuasithinUnique.Bridge.Over.CertA5.D_le hD
    (card_eq_of_isSylowTwoOf_top hD (k := 2) (m := 15)
      (by rw [CFSG.QuasithinUnique.Bridge.Over.CertA5.card_alt]; norm_num) (by decide))
    (by decide)

theorem noFiveOver_alt6 :
    NoFiveOver ↥(alternatingGroup (Fin 6)) := by
  have hD := CFSG.QuasithinUnique.L246C127.Even6.isSylow_D
  exact noFiveOver_alt_of_cert CFSG.QuasithinUnique.L246C127.Even6.cert
    CFSG.QuasithinUnique.L246C127.Even6.cert_check
    CFSG.QuasithinUnique.L246C127.Even6.closure_mGens
    CFSG.QuasithinUnique.L246C127.Even6.D_le hD
    (card_eq_of_isSylowTwoOf_top hD (k := 3) (m := 45)
      (by rw [CFSG.QuasithinUnique.L246C127.Even6.card_alt]; norm_num) (by decide))
    (by decide)

theorem noFiveOver_alt8 :
    NoFiveOver ↥(alternatingGroup (Fin 8)) := by
  have hD := CFSG.QuasithinUnique.L246C127.Even8.isSylow_D
  exact noFiveOver_alt_of_cert CFSG.QuasithinUnique.L246C127.Even8.cert
    CFSG.QuasithinUnique.L246C127.Even8.cert_check
    CFSG.QuasithinUnique.L246C127.Even8.closure_mGens
    CFSG.QuasithinUnique.L246C127.Even8.D_le hD
    (card_eq_of_isSylowTwoOf_top hD (k := 6) (m := 315)
      (by rw [CFSG.QuasithinUnique.L246C127.Even8.card_alt]; norm_num) (by decide))
    (by decide)

end CFSG.Quasithin.H13.FiveNorm
