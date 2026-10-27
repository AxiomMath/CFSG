module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSTI
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenW
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixDefs
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixLen2

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (C : Cfg G M X n)

@[expose] def thetaPre (F : Subgroup (Perm (Fin n))) : Subgroup G :=
  (F.comap C.θ).map M.subtype

theorem mem_thetaPre {F : Subgroup (Perm (Fin n))} {g : G} :
    g ∈ C.thetaPre F ↔ ∃ hg : g ∈ M, C.θ ⟨g, hg⟩ ∈ F := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem thetaPre_le_M (F : Subgroup (Perm (Fin n))) : C.thetaPre F ≤ M := by
  rintro _ ⟨m, -, rfl⟩
  exact m.2

theorem thetaPre_mono {F F' : Subgroup (Perm (Fin n))} (h : F ≤ F') :
    C.thetaPre F ≤ C.thetaPre F' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem Q_le_thetaPre (hR : Nat.card ↥(Rc X) ≤ 2) (F : Subgroup (Perm (Fin n))) :
    CFSG.Open.pCoreOf 2 M ≤ C.thetaPre F := by
  intro q hq
  have hqM : q ∈ M := pCoreOf_le_self M hq
  refine C.mem_thetaPre.2 ⟨hqM, ?_⟩
  have : (⟨q, hqM⟩ : ↥M) ∈ C.θ.ker := by
    rw [C.theta_ker_eq hR]
    exact hq
  rw [MonoidHom.mem_ker] at this
  rw [this]
  exact F.one_mem

theorem theta_thetaPre (hsurj : Function.Surjective C.θ) (F : Subgroup (Perm (Fin n))) :
    ((C.thetaPre F).subgroupOf M).map C.θ = F := by
  have h : (C.thetaPre F).subgroupOf M = F.comap C.θ :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  rw [h]
  exact Subgroup.map_comap_eq_self_of_surjective hsurj F

theorem eq_thetaPre (hR : Nat.card ↥(Rc X) ≤ 2) {N : Subgroup G}
    (hQN : CFSG.Open.pCoreOf 2 M ≤ N) (hNM : N ≤ M) :
    N = C.thetaPre ((N.subgroupOf M).map C.θ) := by
  ext g
  rw [C.mem_thetaPre]
  constructor
  · intro hg
    exact ⟨hNM hg, Subgroup.mem_map.2 ⟨⟨g, hNM hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩⟩
  · rintro ⟨hgM, hmem⟩
    obtain ⟨⟨n', hn'M⟩, hn', hθ⟩ := Subgroup.mem_map.1 hmem
    have hn'N : n' ∈ N := hn'
    have hker : (⟨n', hn'M⟩ : ↥M)⁻¹ * ⟨g, hgM⟩ ∈ C.θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, inv_mul_cancel]
    rw [C.theta_ker_eq hR, Subgroup.mem_subgroupOf] at hker
    have hQg : n'⁻¹ * g ∈ N := hQN hker
    simpa using N.mul_mem hn'N hQg

end Cfg

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G}

abbrev T2 (C : Cfg G M X 6) (i j : Fin 6) : Subgroup G :=
  C.thetaPre (Subgroup.zpowers (swap i j))

noncomputable abbrev T1 (C : Cfg G M X 6) (i j : Fin 6) : Subgroup G :=
  C.thetaPre (klein4 ({i, j}ᶜ : Finset (Fin 6)))

end Cfg

section Vec

variable {n : ℕ}

theorem vecPerm_indVec_of_mem_setStab {I : Finset (Fin n)} {σ : Perm (Fin n)}
    (hσ : σ ∈ setStab I) : vecPerm σ (indVec I) = indVec I := by
  funext i
  rw [vecPerm_apply]
  have h := mem_setStab.1 hσ (σ⁻¹ i)
  have e : σ (σ⁻¹ i) = i := by simp
  rw [e] at h
  by_cases hi : σ⁻¹ i ∈ I
  · rw [show indVec I (σ⁻¹ i) = 1 from if_pos hi, show indVec I i = 1 from if_pos (h.2 hi)]
  · rw [show indVec I (σ⁻¹ i) = 0 from if_neg hi,
      show indVec I i = 0 from if_neg fun hi' => hi (h.1 hi')]

theorem evenWeightPerm_eq_self_of_mem_setStab {I : Finset (Fin n)} {σ : Perm (Fin n)}
    (hσ : σ ∈ setStab I) {u : evenWeight n}
    (hu : (∀ i, (u : Fin n → ZMod 2) i = indVec I i) ∨
      (∀ i, (u : Fin n → ZMod 2) i = indVec I i + 1)) : evenWeightPerm σ u = u := by
  apply Subtype.ext
  funext i
  rw [evenWeightPerm_apply]
  have hI : indVec I (σ⁻¹ i) = indVec I i := by
    simpa [vecPerm_apply] using congrFun (vecPerm_indVec_of_mem_setStab hσ) i
  rcases hu with h0 | h1
  · rw [h0, h0, hI]
  · rw [h1, h1, hI]

end Vec

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

theorem comm_of_barAct_eq_len_two (hR : Nat.card ↥(Rc X) ≤ 2) {y : G}
    (hy : y ∈ CFSG.Open.pCoreOf 2 M) (hl : barLen (Multiplicative.toAdd (D.piQ ⟨y, hy⟩)) = 2)
    {m : ↥M} (hm : barAct (C.θ m) (Multiplicative.toAdd (D.piQ ⟨y, hy⟩)) =
      Multiplicative.toAdd (D.piQ ⟨y, hy⟩)) :
    (m : G) * y * (m : G)⁻¹ = y := by
  classical
  obtain ⟨I, hIc, hvI⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ ⟨y, hy⟩))
  rw [hl] at hIc
  have hsum : ∑ i, indVec I i = 0 := by
    have h : ∑ i, indVec I i = (I.card : ZMod 2) := by simp [indVec, Finset.sum_boole]
    rw [h, hIc]
    decide
  have hrange : Multiplicative.toAdd (D.piQ ⟨y, hy⟩) ∈ Set.range (heartToBar (n := 6)) := by
    rw [hvI]
    exact mk_mem_range_heartToBar hsum
  obtain ⟨w, hw, r, hr, hywr⟩ := D.exists_mul_of_mem_range hrange
  have hywr' : y = w * r := hywr
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
    have h := hr
    rw [C.S.R_eq_inf] at h
    exact (Subgroup.mem_inf.1 h).1
  obtain ⟨ψ, hψβ, hψM, hψsurj⟩ := C.exists_psi0
  obtain ⟨a, ha₀⟩ := hψsurj ⟨w, hw⟩
  obtain ⟨u, ha⟩ : ∃ u : evenWeight 6, ψ (Multiplicative.ofAdd u) = ⟨w, hw⟩ :=
    ⟨Multiplicative.toAdd a, ha₀⟩
  have hπy : Multiplicative.toAdd (D.piQ ⟨y, hy⟩) = ((u : Fin 6 → ZMod 2) : permBar 6) := by
    have hyq : (⟨y, hy⟩ : ↥(CFSG.Open.pCoreOf 2 M)) =
        ⟨w, C.S.W_le_Q hw⟩ * ⟨r, hrQ⟩ := Subtype.ext hywr'
    have h1 : D.piQ ⟨r, hrQ⟩ = 1 := (D.piQ_eq_one_iff ⟨r, hrQ⟩).2 hr
    have h2 : D.piQ ⟨y, hy⟩ = D.piQ ⟨w, C.S.W_le_Q hw⟩ := by
      rw [hyq, map_mul, h1, mul_one]
    rw [h2, D.piQ_W ⟨w, hw⟩ ⟨w, C.S.W_le_Q hw⟩ rfl]
    have h3 : C.β ⟨w, hw⟩ = C.β (ψ (Multiplicative.ofAdd u)) := by rw [ha]
    rw [h3, hψβ u, heartToBar_mk]
  have hbar : ((indVec I : Fin 6 → ZMod 2) : permBar 6) = ((u : Fin 6 → ZMod 2) : permBar 6) :=
    hvI.symm.trans hπy
  have hu := bar_mk_eq_iff.1 hbar
  have hσ : C.θ m ∈ setStab I := by
    have h := hm
    rw [hvI] at h
    exact (barAct_barInd_eq_self_iff (by omega) _).1 h
  have hfix : evenWeightPerm (C.θ m) u = u := evenWeightPerm_eq_self_of_mem_setStab hσ hu
  have hMw : (m : G) * w * (m : G)⁻¹ = w := by
    have h := hψM m u
    rw [hfix, ha] at h
    exact h
  have hMr : (m : G) * r * (m : G)⁻¹ = r := C.R_central hR m m.2 r hr
  calc (m : G) * y * (m : G)⁻¹ = ((m : G) * w * (m : G)⁻¹) * ((m : G) * r * (m : G)⁻¹) := by
        rw [hywr']; group
    _ = y := by rw [hMw, hMr, hywr']

theorem card_M_eq_fifteen (hR : Nat.card ↥(Rc X) ≤ 2) {y : G}
    (hy : y ∈ CFSG.Open.pCoreOf 2 M) (hl : barLen (Multiplicative.toAdd (D.piQ ⟨y, hy⟩)) = 2) :
    Nat.card ↥M = 15 * Nat.card ↥(CMOf M y) := by
  set v := Multiplicative.toAdd (D.piQ ⟨y, hy⟩)
  have h1 := C.card_M_eq_six v
  rw [hl, SixS.card_barLen_two] at h1
  have h2 : Nat.card ↥(CMOf M y) ≤ Nat.card ↥(H4b.barStab C v) :=
    H4b.card_CMOf_le_barStab D ⟨y, hy⟩
  have h3 : Nat.card ↥(H4b.barStab C v) ≤ Nat.card ↥(CMOf M y) := by
    have hle : H4b.barStab C v ≤ (CMOf M y).subgroupOf M := fun m hm =>
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨m.2,
        mem_centralizer_zpowers_iff.2 (D.comm_of_barAct_eq_len_two hR hy hl hm)⟩)
    have e : Nat.card ↥((CMOf M y).subgroupOf M) = Nat.card ↥(CMOf M y) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [← e]
    exact Subgroup.card_le_of_le hle
  rw [h1, le_antisymm h3 h2]

end Cfg.PiData

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

theorem piQ_bijective_of_bot (hRb : Rc X = ⊥)
    (hQ16 : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16) : Function.Bijective D.piQ := by
  classical
  have hinj : Function.Injective D.piQ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have h : (q : G) ∈ Rc X := (D.piQ_eq_one_iff q).1 hq
    rw [hRb, Subgroup.mem_bot] at h
    exact Subtype.ext h
  refine ⟨hinj, ?_⟩
  let f : Multiplicative (altHeart 6) →* Multiplicative (permBar 6) :=
    AddMonoidHom.toMultiplicative heartToBar
  have hfinj : Function.Injective f := fun a b h => heartToBar_injective h
  have hfcard : Nat.card f.range = 16 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, Nat.card_congr Multiplicative.toAdd,
      SimsTheoremC.card_altHeart_even (by norm_num) (by decide)]
    norm_num
  have hfle : f.range ≤ D.piQ.range := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨q, -, hq⟩ := Subgroup.mem_map.1 (D.heart_mem_piQ_Q (Multiplicative.toAdd a))
    exact ⟨q, hq⟩
  have hdvd1 : 16 ∣ Nat.card D.piQ.range := hfcard ▸ Subgroup.card_dvd_of_le hfle
  have hVcard : Nat.card (Multiplicative (permBar 6)) = 32 := by
    rw [Nat.card_congr Multiplicative.toAdd, Comb.card_permBar (by norm_num)]
    norm_num
  have hdvd2 : Nat.card D.piQ.range ∣ 32 :=
    hVcard ▸ Subgroup.card_subgroup_dvd_card D.piQ.range
  have hr : Nat.card D.piQ.range = Nat.card ↥(CFSG.Open.pCoreOf 2 M) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hle32 : Nat.card D.piQ.range ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd2
  have hpos : 0 < Nat.card D.piQ.range := Nat.card_pos
  have h32 : Nat.card D.piQ.range = 32 := by omega
  have htop : D.piQ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (h32.trans hVcard.symm)
  exact MonoidHom.range_eq_top.1 htop

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
