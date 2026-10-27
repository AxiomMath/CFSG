module

public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.CharacterTheory.Semidihedral.CentralHall
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.Theta.TwoPlane

open CFSG CFSG.RankThree.GroupTheory

variable {H K : Type*} [Group H] [Group K]

theorem conj_mem_centralizer_of_map_commute (f : H →* K) (hcen : f.ker ≤ Subgroup.center H)
    {h y g : H} (hyh : f y * f h = f h * f y)
    (hg : g ∈ Subgroup.centralizer ({h} : Set H)) :
    y * g * y⁻¹ ∈ Subgroup.centralizer ({h} : Set H) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  set z := h⁻¹ * (y⁻¹ * h * y) with hz
  have hzker : z ∈ f.ker := by
    rw [MonoidHom.mem_ker, hz]
    simp only [map_mul, map_inv]
    rw [mul_assoc (f y)⁻¹ (f h) (f y), ← hyh, inv_mul_cancel_left, inv_mul_cancel]
  have hzc := Subgroup.mem_center_iff.mp (hcen hzker)
  have hconj : y⁻¹ * h * y = h * z := by rw [hz]; group
  have hg' : (h * z) * g = g * (h * z) := by
    rw [mul_assoc, ← hzc g, ← mul_assoc, ← hg, mul_assoc]
  calc y * g * y⁻¹ * h = y * (g * (y⁻¹ * h * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * h * y) * g) * y⁻¹ := by rw [hconj, hg']
    _ = h * (y * g * y⁻¹) := by group

theorem mem_normalizer_centralizer_of_map_commute (f : H →* K)
    (hcen : f.ker ≤ Subgroup.center H) {h y : H} (hyh : f y * f h = f h * f y) :
    y ∈ Subgroup.normalizer (Subgroup.centralizer ({h} : Set H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_centralizer_of_map_commute f hcen hyh, fun hg => ?_⟩
  have hyh' : f y⁻¹ * f h = f h * f y⁻¹ := by
    rw [map_inv]
    calc (f y)⁻¹ * f h = (f y)⁻¹ * (f h * f y) * (f y)⁻¹ := by group
      _ = (f y)⁻¹ * (f y * f h) * (f y)⁻¹ := by rw [hyh]
      _ = f h * (f y)⁻¹ := by group
  have := conj_mem_centralizer_of_map_commute f hcen hyh' hg
  simpa [mul_assoc] using this

theorem map_inSubgroup_pCore_centralizer_le (f : H →* K) (hf : Function.Surjective f)
    (hcen : f.ker ≤ Subgroup.center H) (h : H) :
    (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({h} : Set H))).map f ≤
      inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({f h} : Set K)) := by
  refine SteinbergBY.le_inSubgroup_pCore ((SteinbergBY.isPGroup_inSubgroup_pCore 2 _).map f)
    ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    have hyc := SteinbergBY.inSubgroup_pCore_le 2 _ hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
    rw [← map_mul, ← map_mul, hyc]
  · intro k hk
    obtain ⟨y, rfl⟩ := hf k
    rw [Subgroup.mem_centralizer_singleton_iff] at hk
    have hy := SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 _
      (mem_normalizer_centralizer_of_map_commute f hcen hk)
    exact Subgroup.le_normalizer_map f ⟨y, hy, rfl⟩

theorem le_pCore_of_map_le [Finite H] [Finite K] (f : H →* K)
    (hcen : f.ker ≤ Subgroup.center H) {S : Subgroup H} (hS : IsPGroup 2 S)
    (hSf : S.map f ≤ CFSG.pCore 2 K) : S ≤ CFSG.pCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := (CFSG.pCore 2 K).comap f with hQ
  have hQn : Q.Normal := (CFSG.pCore_normal (p := 2) (G := K)).comap f
  have hQnil : Group.IsNilpotent Q := by
    let g : Q →* CFSG.pCore 2 K := (f.comp Q.subtype).codRestrict (CFSG.pCore 2 K) fun x => x.2
    have : Group.IsNilpotent (CFSG.pCore 2 K) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center g fun x hx => ?_
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : (x : H) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hcen hx') y)
  have hSQ : S ≤ Q := Subgroup.map_le_iff_le_comap.mp hSf
  have hS' : IsPGroup 2 (S.subgroupOf Q) := hS.comap_of_injective Q.subtype Q.subtype_injective
  obtain ⟨P, hP⟩ := hS'.exists_le_sylow
  calc S = (S.subgroupOf Q).map Q.subtype := (Subgroup.map_subgroupOf_eq_of_le hSQ).symm
    _ ≤ (P : Subgroup Q).map Q.subtype := Subgroup.map_mono hP
    _ ≤ CFSG.pCore 2 H := Sylow.map_le_pCore hQn hQnil 2 P

theorem pCore_two_eq_map_of_central_kernel [Finite H] [Finite K] (f : H →* K)
    (hf : Function.Surjective f) (hcen : f.ker ≤ Subgroup.center H)
    (hodd : Odd (Nat.card f.ker)) : CFSG.pCore 2 K = (CFSG.pCore 2 H).map f := by
  refine le_antisymm ?_ (le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := H)).map f hf,
    (CFSG.pCore_isPGroup (p := 2) (G := H)).map f⟩)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V := (CFSG.pCore 2 K).comap f
  have hVn : V.Normal := (CFSG.pCore_normal (p := 2) (G := K)).comap f
  have hkV : f.ker ≤ V := fun x hx => by
    change f x ∈ CFSG.pCore 2 K
    rw [MonoidHom.mem_ker.1 hx]
    exact one_mem _
  let A : Subgroup V := f.ker.subgroupOf V
  have hA : A ≤ Subgroup.center V := fun x hx => by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hcen hx) y)
  let g : V →* CFSG.pCore 2 K := (f.comp V.subtype).codRestrict _ fun v => v.2
  have hg : Function.Surjective g := by
    rintro ⟨k, hk⟩
    obtain ⟨x, rfl⟩ := hf k
    exact ⟨⟨x, hk⟩, rfl⟩
  have hgker : g.ker = A := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hindex : A.index = Nat.card (CFSG.pCore 2 K) := by
    rw [← hgker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hg, Subgroup.card_top]
  have hAcard : Nat.card A = Nat.card f.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkV).toEquiv
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := K))
  have hcop : (Nat.card A).Coprime A.index := by
    rw [hindex, hAcard, hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd)
  obtain ⟨T, hTchar, hTcard, -, -, -, -, -, -, -, e, he⟩ :=
    Semidihedral.central_hall_subgroup_direct_complement A hA hcop
  have hTn : (T.map V.subtype).Normal := by
    have := hVn
    have := hTchar
    infer_instance
  have hT2 : IsPGroup 2 (T.map V.subtype) := IsPGroup.of_card (n := n) (by
    rw [Subgroup.card_map_of_injective V.subtype_injective, hTcard, hindex, hn])
  have hTle : T.map V.subtype ≤ CFSG.pCore 2 H := le_sSup ⟨hTn, hT2⟩
  intro k hk
  obtain ⟨x, rfl⟩ := hf k
  have hxV : x ∈ V := hk
  obtain ⟨⟨a, t⟩, hat⟩ := e.surjective ⟨x, hxV⟩
  have hx : x = (a : H) * (t : H) := (congrArg Subtype.val ((he a t).symm.trans hat)).symm
  have ha : f (a : H) = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_subgroupOf.1 a.2)
  exact ⟨(t : H), hTle ⟨t, t.2, rfl⟩, by rw [hx, map_mul, ha, one_mul]⟩

theorem map_twoCoreX_le (f : H →* K) (hf : Function.Surjective f)
    (hcen : f.ker ≤ Subgroup.center H) (P : Subgroup H) :
    (twoCoreX P).map f ≤ twoCoreX (P.map f) := by
  intro k hk
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hk
  rw [mem_twoCoreX_iff] at hy ⊢
  rintro _ ⟨b, hb, rfl⟩ hb1
  have hb1' : b ≠ 1 := fun h => hb1 (by rw [h, map_one])
  exact map_inSubgroup_pCore_centralizer_le f hf hcen b ⟨y, hy b hb hb1', rfl⟩

theorem map_twoCoreJ_le (f : H →* K) (hf : Function.Surjective f)
    (hcen : f.ker ≤ Subgroup.center H) {P : Subgroup H} (hdisj : Disjoint P f.ker) :
    (twoCoreJ P).map f ≤ twoCoreJ (P.map f) := by
  rw [twoCoreJ, Subgroup.map_iSup]
  refine iSup_le fun b => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hb => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hb1 => ?_
  have hfb : f b ≠ 1 := fun h =>
    hb1 ((Subgroup.disjoint_def.mp hdisj) hb (MonoidHom.mem_ker.mpr h))
  rw [Subgroup.map_commutator]
  exact (Subgroup.commutator_mono (map_inSubgroup_pCore_centralizer_le f hf hcen b) le_rfl).trans
    (commutator_le_twoCoreJ (Subgroup.mem_map_of_mem f hb) hfb)

theorem twoCoreAlpha_le_pCore_of_map [Finite H] [Finite K] (f : H →* K)
    (hf : Function.Surjective f) (hcen : f.ker ≤ Subgroup.center H) {P : Subgroup H}
    (hPc : IsMulCommutative P) (hP : P ≠ ⊥) (hdisj : Disjoint P f.ker)
    (hα : twoCoreAlpha (P.map f) ≤ CFSG.pCore 2 K) :
    twoCoreAlpha P ≤ CFSG.pCore 2 H := by
  have hPC : ∀ b ∈ P, P ≤ Subgroup.centralizer ({b} : Set H) := fun b hb x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hPc.is_comm.comm ⟨x, hx⟩ ⟨b, hb⟩))
  have hPN : ∀ b ∈ P, P ≤ Subgroup.normalizer
      (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b} : Set H)) : Set H) := fun b hb =>
    (hPC b hb).trans (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _)
  refine sup_le ?_ ?_
  · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    have hle := Subgroup.le_normalizer_iff_commutator_le_left.mp (hPN b hb)
    refine le_pCore_of_map_le f hcen ((SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le hle) ?_
    refine le_trans ?_ hα
    refine le_trans ?_ (twoCoreJ_le_twoCoreAlpha _)
    refine le_trans ?_ (map_twoCoreJ_le f hf hcen hdisj)
    exact Subgroup.map_mono (commutator_le_twoCoreJ hb hb1)
  · obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP
    have hb₀1' : b₀ ≠ 1 := fun h => hb₀1 (Subtype.ext h)
    have hX2 : IsPGroup 2 (twoCoreX P) :=
      (SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le fun x hx =>
        mem_twoCoreX_iff.mp hx b₀ hb₀ hb₀1'
    exact le_pCore_of_map_le f hcen hX2
      ((map_twoCoreX_le f hf hcen P).trans ((twoCoreX_le_twoCoreAlpha _).trans hα))

end CFSG.RankThree.Theta.TwoPlane
