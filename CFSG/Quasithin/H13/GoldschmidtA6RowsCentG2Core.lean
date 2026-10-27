module

public import CFSG.Quasithin.H13.GoldschmidtA6RowsFrame
public import CFSG.Quasithin.H13.GoldschmidtA6RowsCentG2Alg

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Matrix

namespace CFSG.Quasithin.H13.A6.GR

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {Γ : Type} [Group Γ] {d : ℕ}

@[expose] def CentLeaf {mat : Γ → Matrix (Fin d) (Fin d) (ZMod 2)} (M : ModelHyp d Γ mat) : Prop :=
  ∀ w : Fin d → ZMod 2, M.cyc.Pmat w * M.cyc.Pmat w = 1 →
    (∀ A ∈ M.cyc.gm, M.cyc.Pmat w * A = A * M.cyc.Pmat w) →
    fixCard (M.cyc.Pmat w) = 2 ^ (d - 2) → ∀ K, M.Mem K →
      K * M.cyc.Pmat w = M.cyc.Pmat w * K →
        K ^ (3 * 2 ^ M.a) = 1 ∧ (K ^ 3 = 1 → K ≠ 1 → Span [K])

theorem fixCard_pm [Finite V] (fr : Frame V L Γ d) (hd : 2 ≤ d) {v : MulAut V}
    (hrk : rkIdx (fixV (Subgroup.zpowers v)) = 2) : fixCard (fr.pm v) = 2 ^ (d - 2) := by
  have h4 := index_eq_four fr.card_V _ hrk
  have hc := Subgroup.card_mul_index (fixV (Subgroup.zpowers v))
  rw [h4, fr.card_V] at hc
  have h5 : Nat.card ↥(fixV (Subgroup.zpowers v)) = 2 ^ (d - 2) := by
    have : 2 ^ d = 2 ^ (d - 2) * 4 := by
      have : d = (d - 2) + 2 := by omega
      conv_lhs => rw [this]
      rw [pow_add]; norm_num
    omega
  rw [fr.card_fixV v] at h5
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h5
  simpa [fixCard] using h5

theorem exists_conj_cyc [Finite V] [Finite Γ] (fr : Frame V L Γ d) (M : ModelHyp d Γ fr.mat)
    {v : MulAut V} (hv2 : v * v = 1) (hrk : rkIdx (fixV (Subgroup.zpowers v)) = 2)
    {S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S L) (hSv : S ≤ Subgroup.centralizer {v}) :
    ∃ (fr' : Frame V L Γ d) (w : Fin d → ZMod 2), fr'.mat = fr.mat ∧ fr'.pm v = M.cyc.Pmat w ∧
      M.cyc.Pmat w * M.cyc.Pmat w = 1 ∧ (∀ A ∈ M.cyc.gm, M.cyc.Pmat w * A = A * M.cyc.Pmat w) ∧
      fixCard (M.cyc.Pmat w) = 2 ^ (d - 2) := by
  obtain ⟨g, hg⟩ := fr.exists_conj_sylow hS M.p2
  set fr' := fr.conj g with hfr'
  have hψ' : ∀ s ∈ M.S0, ((fr'.ψ s : ↥L) : MulAut V) ∈ S := fun s hs => hg s hs
  set P := fr'.pm v with hP
  have hPP : P * P = 1 := by rw [hP, ← Frame.pm_mul, hv2, Frame.pm_one]
  have hcommgm : ∀ A ∈ M.cyc.gm, P * A = A * P := by
    intro A hA
    rw [M.cyc_gm, List.mem_map] at hA
    obtain ⟨s, hs, rfl⟩ := hA
    refine Frame.pm_comm fr' s rfl ?_
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hSv (hψ' s (M.gens_mem s hs)))).symm
  have hPcyc : P = M.cyc.Pmat (P *ᵥ M.cyc.u) := M.cyc.eq_Pmat M.hB hcommgm
  refine ⟨fr', P *ᵥ M.cyc.u, rfl, hPcyc, ?_, ?_, ?_⟩
  · rw [← hPcyc]; exact hPP
  · rw [← hPcyc]; exact hcommgm
  · rw [← hPcyc]; exact fixCard_pm fr' M.hd hrk

theorem cent_core [Finite V] [Finite Γ] (fr : Frame V L Γ d) (M : ModelHyp d Γ fr.mat)
    (hM : CentLeaf M) {v : MulAut V} (hv2 : v * v = 1)
    (hrk : rkIdx (fixV (Subgroup.zpowers v)) = 2) {S Pg : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S L) (hSv : S ≤ Subgroup.centralizer {v}) (hPL : Pg ≤ L)
    (hPC : Pg ≤ Subgroup.centralizer {v}) (hP9 : Nat.card Pg = 9) : False := by
  obtain ⟨fr', w, hmat, hPw, hPP, hPA, hfix⟩ := exists_conj_cyc fr M hv2 hrk hS hSv
  set Q : Subgroup Γ := (Pg.subgroupOf L).comap fr'.ψ with hQ
  have hQcard : Nat.card Q = 9 := by
    have hmap : Q.map fr'.ψ = Pg.subgroupOf L :=
      Subgroup.map_comap_eq_self_of_surjective fr'.bij.2 _
    have hc : Nat.card Q = Nat.card Pg := by
      rw [← Subgroup.card_map_of_injective fr'.bij.1, hmap]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
    rw [hc, hP9]
  have hKP : ∀ γ ∈ Q, fr'.mat γ * M.cyc.Pmat w = M.cyc.Pmat w * fr'.mat γ := by
    intro γ hγ
    rw [← hPw]
    have hγP : ((fr'.ψ γ : ↥L) : MulAut V) ∈ Pg := hγ
    exact (Frame.pm_comm fr' (v := v) γ rfl
      (Subgroup.mem_centralizer_singleton_iff.mp (hPC hγP)).symm).symm
  have key : ∀ γ ∈ Q, γ ^ 3 = 1 ∧ (γ ≠ 1 → IsUnit (fr'.mat γ - 1)) := by
    intro γ hγ
    obtain ⟨hKE, hsp⟩ := hM w hPP hPA hfix (fr'.mat γ) (by rw [hmat]; exact M.hMem γ) (hKP γ hγ)
    have hγ9 : γ ^ 9 = 1 := by
      have h := pow_card_eq_one' (G := Q) (x := ⟨γ, hγ⟩)
      rw [hQcard] at h
      exact congrArg Subtype.val h
    have hK9 : fr'.mat γ ^ 9 = 1 := by rw [← Frame.mat_pow, hγ9, Frame.mat_one]
    have hK3 : fr'.mat γ ^ 3 = 1 := pow_three_of_odd _ M.a 9 (by decide) hK9 hKE
    refine ⟨fr'.eq_one_of_mat (by rw [Frame.mat_pow, hK3]), fun hγ1 => ?_⟩
    exact isUnit_sub_one_of_span (hsp hK3 fun h1 => hγ1 (fr'.eq_one_of_mat h1))
  let ρ : ↥Q →* Matrix (Fin d) (Fin d) (ZMod 2) :=
    { toFun := fun q => fr'.mat q.1
      map_one' := Frame.mat_one fr'
      map_mul' := fun a b => Frame.mat_mul fr' a.1 b.1 }
  exact false_of_fpf_nine hQcard (fun q => Subtype.ext (key q.1 q.2).1) ρ
    (fun q hq => Subtype.ext (fr'.eq_one_of_mat hq))
    fun q hq1 => (key q.1 q.2).2 fun h => hq1 (Subtype.ext h)

end CFSG.Quasithin.H13.A6.GR
