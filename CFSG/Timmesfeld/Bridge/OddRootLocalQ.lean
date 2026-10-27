module

public import CFSG.Timmesfeld.Bridge.OddRootCompl
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.BenderSuzuki CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem rootGroup_eq_sup
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) {C S : Subgroup G} (hC : GoodCompl D d x C S) :
    rootGroup D d = S ⊔ Wof D d x := by
  apply le_antisymm
  · rw [rootGroup, Subgroup.closure_le]
    intro e he
    obtain ⟨w, hw, s, hs, rfl⟩ := rootSet_subset_Wof_mul_sylow h hd hx hdx hpx hC he
    exact Subgroup.mul_mem (S ⊔ Wof D d x) (Subgroup.mem_sup_right hw)
      (Subgroup.mem_sup_left hs)
  · refine sup_le ?_ (Wof_le_rootGroup d x)
    intro s hs
    by_cases h1 : s = 1
    · rw [h1]; exact (rootGroup D d).one_mem
    · exact rootSet_subset_rootGroup D d (hC.S_root s hs h1)

theorem Qof_eq_closure
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) {C S : Subgroup G} (hC : GoodCompl D d x C S) :
    Qof D d x = Subgroup.closure {g | ∃ c ∈ C, ∃ w ∈ Wof D d x, g = c * w * c⁻¹} := by
  let N₀ : Subgroup G :=
    Subgroup.closure {g | ∃ c ∈ C, ∃ w ∈ Wof D d x, g = c * w * c⁻¹}
  change Qof D d x = N₀
  have hN₀Q : N₀ ≤ Qof D d x := by
    rw [show N₀ = Subgroup.closure {g | ∃ c ∈ C, ∃ w ∈ Wof D d x, g = c * w * c⁻¹} from rfl,
      Subgroup.closure_le]
    rintro g ⟨c, hc, w, hw, rfl⟩
    exact conj_mem_Qof d x (hC.le hc) (Wof_le_Qof d x hw)
  have hforward : ∀ c ∈ C, ∀ g ∈ N₀, c * g * c⁻¹ ∈ N₀ := by
    intro c hc g hg
    rw [show N₀ = Subgroup.closure {g | ∃ c ∈ C, ∃ w ∈ Wof D d x, g = c * w * c⁻¹}
      from rfl] at hg ⊢
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c₀, hc₀, w, hw, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨c * c₀, C.mul_mem hc hc₀, w, hw, by group⟩
    | one => simp
    | mul x y hx hy ihx ihy =>
      rw [show c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) from by group]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih =>
      rw [show c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ from by group]
      exact Subgroup.inv_mem _ ih
  have hN₀norm : C ≤ Subgroup.normalizer (N₀ : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact hforward c hc g
    · intro hg
      have h := hforward c⁻¹ (C.inv_mem hc) (c * g * c⁻¹) hg
      have e : c⁻¹ * (c * g * c⁻¹) * c⁻¹⁻¹ = g := by group
      rwa [e] at h
  have hEd : rootSet D d ⊆ (N₀ : Set G) * (C : Set G) := by
    intro e he
    obtain ⟨w, hw, s, hs, rfl⟩ := rootSet_subset_Wof_mul_sylow h hd hx hdx hpx hC he
    exact ⟨w, Subgroup.subset_closure ⟨1, C.one_mem, w, hw, by simp⟩, s, hC.S_le hs, rfl⟩
  have hXC : rootGen D d x ≤ N₀ ⊔ C := by
    rw [rootGen, Subgroup.closure_le]
    rintro z (rfl | hz)
    · exact Subgroup.mem_sup_right hC.x_mem
    · obtain ⟨w, hw, s, hs, rfl⟩ := hEd hz
      exact Subgroup.mul_mem (N₀ ⊔ C) (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hs)
  apply le_antisymm _ hN₀Q
  intro q hq
  have hqC' : q ∈ (↑(N₀ ⊔ C) : Set G) := hXC (Qof_le_rootGen d x hq)
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N₀ C hN₀norm] at hqC'
  obtain ⟨n, hn, c, hc, hnc⟩ := Set.mem_mul.mp hqC' 
  have hcQ : c ∈ Qof D d x := by
    have : c = n⁻¹ * q := by rw [← hnc]; group
    rw [this]
    exact (Qof D d x).mul_mem ((Qof D d x).inv_mem (hN₀Q hn)) hq
  have hc1 : c = 1 := by
    have hmem : c ∈ C ⊓ Qof D d x := ⟨hc, hcQ⟩
    rw [hC.inf] at hmem
    exact Subgroup.mem_bot.mp hmem
  rw [← hnc, hc1, mul_one]
  exact hn


theorem Qof_comm
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) (hpx' : PSL2Pair D x d) :
    Qof D d x = Qof D x d := by
  have hX : rootGen D d x = rootGen D x d := rootGen_comm h hd hx hdx hpx hpx'
  simp only [Qof]
  rw [hX]

theorem rootGen_eq_rootGroup_sup
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) :
    rootGen D d x = rootGroup D d ⊔ rootGroup D x := by
  apply le_antisymm
  · rw [rootGen, Subgroup.closure_le]
    intro e he
    rcases Set.mem_insert_iff.mp he with heq | he
    · rw [heq]
      exact Subgroup.mem_sup_right (rootSet_subset_rootGroup D x (mem_rootSet_self hx))
    · exact Subgroup.mem_sup_left (rootSet_subset_rootGroup D d he)
  · refine sup_le (rootGroup_le_rootGen d x) ?_
    rw [rootGroup, Subgroup.closure_le]
    intro e he
    exact rootSet_subset_rootGen h hd hx hdx hpx he

theorem rootGroup_inf_le_centralizer
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) :
    rootGroup D d ⊓ rootGroup D x ≤ Subgroup.centralizer (rootGen D d x : Set G) := by
  rw [rootGen_eq_rootGroup_sup h hd hx hdx hpx]
  have hA : (rootGroup D d ⊓ rootGroup D x) ≤ Subgroup.centralizer (rootGroup D d : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (commute_of_mem_rootGroup hd hz.1 ha).symm
  have hB : (rootGroup D d ⊓ rootGroup D x) ≤ Subgroup.centralizer (rootGroup D x : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (commute_of_mem_rootGroup hx hz.2 hb).symm
  exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hA hB

theorem rootGroup_inf_le_Qof
    (h : Hyp G D) {d x : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
    (hpx : PSL2Pair D d x) :
    rootGroup D d ⊓ rootGroup D x ≤ Qof D d x := by
  let X := rootGen D d x
  let Q : Subgroup X := CFSG.pCore 2 X
  let π : X →* X ⧸ Q := QuotientGroup.mk' Q
  let I : Subgroup G := rootGroup D d ⊓ rootGroup D x
  let J : Subgroup X := Subgroup.comap X.subtype I
  have hI : I ≤ Subgroup.centralizer (X : Set G) := by
    simpa only [I, X] using rootGroup_inf_le_centralizer h hd hx hdx hpx
  have hZ : Subgroup.map π J ≤ Subgroup.center (X ⧸ Q) := by
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨j, hj, rfl⟩ := hz
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q y
    have hjI : (j : G) ∈ I := by
      have := hj
      rwa [Subgroup.mem_comap] at this
    have hcomm : Commute (g : X) j := by
      have h := (Subgroup.mem_centralizer_iff.mp (hI hjI)) (g : G) g.2
      exact Subtype.ext (by simpa using h)
    rw [← map_mul, ← map_mul]
    exact congrArg π hcomm.eq
  obtain ⟨n, hn, ⟨e⟩⟩ := hpx
  have hcenter : Subgroup.center (X ⧸ Q) = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e
      (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField 2 n))
  have hmapbot : Subgroup.map π J = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' := hZ hz
    rw [hcenter] at hz'
    exact Subgroup.mem_bot.mp hz'
  have hJQ : J ≤ Q := by
    intro j hj
    have h1 : π j = 1 := by
      have : π j ∈ Subgroup.map π J := Subgroup.mem_map_of_mem π hj
      rw [hmapbot] at this
      simpa using this
    rwa [← QuotientGroup.ker_mk' Q, MonoidHom.mem_ker]
  intro i hi
  have hiX : i ∈ X := rootGroup_le_rootGen d x hi.1
  have hiJ : (⟨i, hiX⟩ : X) ∈ J := by
    show (i : G) ∈ I
    exact hi
  exact ⟨⟨i, hiX⟩, hJQ hiJ, rfl⟩


end CFSG.Timmesfeld.Bridge.OddRoot
