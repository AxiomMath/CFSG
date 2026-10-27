module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

private theorem mul_comm_of_conj_eq {G : Type*} [Group G] {N : Subgroup G} {g g' : G}
    (h : ∀ k ∈ N, g * k * g⁻¹ = g' * k * g'⁻¹) :
    ∀ k ∈ N, (g⁻¹ * g') * k = k * (g⁻¹ * g') := by
  intro k hk
  have h1 : (g⁻¹ * g') * k * (g⁻¹ * g')⁻¹ = k := by
    have h2 : g⁻¹ * (g * k * g⁻¹) * g = g⁻¹ * (g' * k * g'⁻¹) * g := by rw [h k hk]
    rw [show g⁻¹ * (g * k * g⁻¹) * g = k from by group] at h2
    calc (g⁻¹ * g') * k * (g⁻¹ * g')⁻¹ = g⁻¹ * (g' * k * g'⁻¹) * g := by group
      _ = k := h2.symm
  calc (g⁻¹ * g') * k = ((g⁻¹ * g') * k * (g⁻¹ * g')⁻¹) * (g⁻¹ * g') := by group
    _ = k * (g⁻¹ * g') := by rw [h1]

private theorem mul_inv_comm {G : Type*} [Group G] {v b c : G}
    (hb : b * v = v * b) (hc : c * v = v * c) : (b * c⁻¹) * v = v * (b * c⁻¹) := by
  have hcinv : c⁻¹ * v = v * c⁻¹ := by
    calc c⁻¹ * v = c⁻¹ * (v * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * v) * c⁻¹ := by rw [← hc]
      _ = v * c⁻¹ := by group
  calc (b * c⁻¹) * v = b * (c⁻¹ * v) := by group
    _ = b * (v * c⁻¹) := by rw [hcinv]
    _ = (b * v) * c⁻¹ := by group
    _ = (v * b) * c⁻¹ := by rw [hb]
    _ = v * (b * c⁻¹) := by group

private def conjAutOfMem {G : Type*} [Group G] {Bs : Subgroup G} (w : G)
    (hw : w ∈ Subgroup.normalizer (Bs : Set G)) : MulAut ↥Bs where
  toFun b := ⟨w * (b : G) * w⁻¹, (Subgroup.mem_normalizer_iff.mp hw (b : G)).mp b.2⟩
  invFun b := ⟨w⁻¹ * (b : G) * w,
    (Subgroup.mem_normalizer_iff.mp hw (w⁻¹ * (b : G) * w)).mpr (by
      rw [show w * (w⁻¹ * (b : G) * w) * w⁻¹ = (b : G) from by group]
      exact b.2)⟩
  left_inv b := by
    apply Subtype.ext
    show w⁻¹ * (w * (b : G) * w⁻¹) * w = (b : G)
    group
  right_inv b := by
    apply Subtype.ext
    show w * (w⁻¹ * (b : G) * w) * w⁻¹ = (b : G)
    group
  map_mul' b b' := by
    apply Subtype.ext
    show w * ((b * b' : ↥Bs) : G) * w⁻¹ =
      (w * (b : G) * w⁻¹) * (w * (b' : G) * w⁻¹)
    rw [Subgroup.coe_mul]
    group

private theorem conjAutOfMem_apply {G : Type*} [Group G] {Bs : Subgroup G} (w : G)
    (hw : w ∈ Subgroup.normalizer (Bs : Set G)) (b : ↥Bs) :
    ((conjAutOfMem w hw b : ↥Bs) : G) = w * (b : G) * w⁻¹ := rfl

theorem ggB48_reduce {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs N : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center ↥N = ⊥)
    (hnorm : Bs ≤ Subgroup.normalizer (N : Set G))
    (hinner : ∀ b ∈ Bs, ∃ g ∈ N, ∀ k ∈ N, b * k * b⁻¹ = g * k * g⁻¹) :
    ∃ E : Subgroup G, E ≤ N ∧ IsElemAbelian p E ∧
      (∀ g ∈ N, g ∈ Subgroup.centralizer (E : Set G) → g ^ p = 1 → g ∈ E) ∧
      ∀ W : Subgroup G, W ≤ N → W ≤ Subgroup.normalizer (E : Set G) →
        (∀ w ∈ W, w ∈ Subgroup.centralizer (E : Set G) → w = 1) →
        Nat.card W ≤ Nat.card (ggAutomizer N Bs) := by
  classical
  have hchoice : ∀ b : ↥Bs, ∃ g : ↥N,
      ∀ k : ↥N, (b : G) * (k : G) * (b : G)⁻¹ = (g : G) * (k : G) * (g : G)⁻¹ := by
    intro b
    obtain ⟨g, hgN, hgk⟩ := hinner (b : G) b.2
    exact ⟨⟨g, hgN⟩, fun k => hgk (k : G) k.2⟩
  choose π hπ using hchoice
  have hcenter : ∀ g : ↥N, (∀ k : ↥N, k * g = g * k) → g = 1 := by
    intro g hg
    have hmem : g ∈ Subgroup.center ↥N := Subgroup.mem_center_iff.mpr (fun k => hg k)
    rw [hZ] at hmem
    exact Subgroup.mem_bot.mp hmem
  have huniq : ∀ (g g' : ↥N),
      (∀ k : ↥N, (g : G) * (k : G) * (g : G)⁻¹ = (g' : G) * (k : G) * (g' : G)⁻¹) →
      g = g' := by
    intro g g' h
    have hcomm : ∀ k : ↥N, k * (g⁻¹ * g') = (g⁻¹ * g') * k := by
      intro k
      have h1 := mul_comm_of_conj_eq (N := N) (g := (g : G)) (g' := (g' : G))
        (fun x hx => h ⟨x, hx⟩) (k : G) k.2
      exact Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1.symm)
    have hz : g⁻¹ * g' = 1 := hcenter (g⁻¹ * g') hcomm
    exact inv_mul_eq_one.mp hz
  have π_mul : ∀ b b' : ↥Bs, π (b * b') = π b * π b' := by
    intro b b'
    apply huniq
    intro k
    calc (π (b * b') : G) * (k : G) * (π (b * b') : G)⁻¹
        = ((b * b' : ↥Bs) : G) * (k : G) * (((b * b' : ↥Bs) : G))⁻¹ := by
          rw [← hπ (b * b') k]
      _ = (b : G) * ((b' : G) * (k : G) * (b' : G)⁻¹) * (b : G)⁻¹ := by
          simp only [Subgroup.coe_mul]
          group
      _ = (b : G) * ((π b' : G) * (k : G) * (π b' : G)⁻¹) * (b : G)⁻¹ := by
          rw [hπ b' k]
      _ = (π b : G) * ((π b' : G) * (k : G) * (π b' : G)⁻¹) * (π b : G)⁻¹ := by
          simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hπ b (π b' * k * (π b')⁻¹)
      _ = ((π b * π b' : ↥N) : G) * (k : G) * (((π b * π b' : ↥N) : G))⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
  have π_mul_G : ∀ b b' : ↥Bs, (π (b * b') : G) = (π b : G) * (π b' : G) :=
    fun b b' => congrArg Subtype.val (π_mul b b')
  let πhom : ↥Bs →* ↥N := MonoidHom.mk' π π_mul
  have π_pow_G : ∀ (b : ↥Bs) (n : ℕ), (π (b ^ n) : G) = (π b : G) ^ n := by
    intro b n
    exact congrArg Subtype.val (map_pow πhom b n)
  have c_comm : ∀ (b : ↥Bs) (k : ↥N),
      ((π b : G)⁻¹ * (b : G)) * (k : G) = (k : G) * ((π b : G)⁻¹ * (b : G)) := by
    intro b k
    have hconj : ((π b : G)⁻¹ * (b : G)) * (k : G) * ((π b : G)⁻¹ * (b : G))⁻¹ = (k : G) := by
      calc ((π b : G)⁻¹ * (b : G)) * (k : G) * ((π b : G)⁻¹ * (b : G))⁻¹
          = (π b : G)⁻¹ * ((b : G) * (k : G) * (b : G)⁻¹) * (π b : G) := by group
        _ = (π b : G)⁻¹ * ((π b : G) * (k : G) * (π b : G)⁻¹) * (π b : G) := by rw [hπ b k]
        _ = (k : G) := by group
    calc ((π b : G)⁻¹ * (b : G)) * (k : G)
        = (((π b : G)⁻¹ * (b : G)) * (k : G) * ((π b : G)⁻¹ * (b : G))⁻¹) *
            ((π b : G)⁻¹ * (b : G)) := by group
      _ = (k : G) * ((π b : G)⁻¹ * (b : G)) := by rw [hconj]
  let E : Subgroup G := (πhom.range).map N.subtype
  have hE_le_N : E ≤ N := Subgroup.map_subtype_le πhom.range
  have hE_mem : ∀ x : G, x ∈ E ↔ ∃ b : ↥Bs, (π b : G) = x := by
    intro x
    constructor
    · intro hx
      rw [show E = (πhom.range).map N.subtype from rfl, Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hy
      exact ⟨b, (congrArg Subtype.val hb).trans hyx⟩
    · rintro ⟨b, rfl⟩
      rw [show E = (πhom.range).map N.subtype from rfl, Subgroup.mem_map]
      exact ⟨π b, MonoidHom.mem_range.mpr ⟨b, rfl⟩, rfl⟩
  have hE_elem : IsElemAbelian p E := by
    constructor
    · refine IsMulCommutative.mk ⟨fun x y => ?_⟩
      obtain ⟨b, hb⟩ := (hE_mem (x : G)).mp x.2
      obtain ⟨b', hb'⟩ := (hE_mem (y : G)).mp y.2
      have hcommBs : b' * b = b * b' := hBs.2.1.1.is_comm.comm b' b
      apply Subtype.ext
      show (x : G) * (y : G) = (y : G) * (x : G)
      calc (x : G) * (y : G) = (π b : G) * (π b' : G) := by rw [← hb, ← hb']
        _ = (π (b * b') : G) := (π_mul_G b b').symm
        _ = (π (b' * b) : G) := by rw [hcommBs]
        _ = (π b' : G) * (π b : G) := π_mul_G b' b
        _ = (y : G) * (x : G) := by rw [hb, hb']
    · intro x hx
      obtain ⟨b, hb⟩ := (hE_mem x).mp hx
      rw [← hb]
      have hbp : (b : ↥Bs) ^ p = 1 := by
        apply Subtype.ext
        simpa using hBs.2.1.2 (b : G) b.2
      calc (π b : G) ^ p = (π (b ^ p) : G) := (π_pow_G b p).symm
        _ = (π (1 : ↥Bs) : G) := by rw [hbp]
        _ = 1 := congrArg Subtype.val (map_one πhom)
  refine ⟨E, hE_le_N, hE_elem, ?_, ?_⟩
  · intro t htN htcent htp
    have htBs : t ∈ Bs := by
      apply hBs.2.2.2 t ?_ htp
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 : (π ⟨b, hb⟩ : G) * t = t * (π ⟨b, hb⟩ : G) :=
        Subgroup.mem_centralizer_iff.mp htcent _ ((hE_mem _).mpr ⟨⟨b, hb⟩, rfl⟩)
      have h2 : ((π ⟨b, hb⟩ : G)⁻¹ * (b : G)) * t =
          t * ((π ⟨b, hb⟩ : G)⁻¹ * (b : G)) := c_comm ⟨b, hb⟩ ⟨t, htN⟩
      have hbdec : b = (π ⟨b, hb⟩ : G) * ((π ⟨b, hb⟩ : G)⁻¹ * (b : G)) := by group
      calc b * t = ((π ⟨b, hb⟩ : G) * ((π ⟨b, hb⟩ : G)⁻¹ * (b : G))) * t :=
              congrArg (fun x => x * t) hbdec
        _ = t * ((π ⟨b, hb⟩ : G) * ((π ⟨b, hb⟩ : G)⁻¹ * (b : G))) := by
              rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
        _ = t * b := (congrArg (fun x => t * x) hbdec).symm
    have hπt : (π ⟨t, htBs⟩ : G) = t :=
      (congrArg Subtype.val (huniq ⟨t, htN⟩ (π ⟨t, htBs⟩) (fun k => hπ ⟨t, htBs⟩ k))).symm
    exact (hE_mem t).mpr ⟨⟨t, htBs⟩, hπt⟩
  · intro W hWN hWnorm hWtriv
    have key : ∀ v ∈ W, ∀ b ∈ Bs, v * b * v⁻¹ ∈ Bs := by
      intro v hvW b hb
      let bs : ↥Bs := ⟨b, hb⟩
      have hbs : (bs : G) = b := rfl
      have hvN : v ∈ N := hWN hvW
      have hvnormE : v ∈ Subgroup.normalizer (E : Set G) := hWnorm hvW
      have hpiE : (π bs : G) ∈ E := (hE_mem _).mpr ⟨bs, rfl⟩
      have hvpiE : v * (π bs : G) * v⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.mp hvnormE (π bs : G)).mp hpiE
      let T : G := (v * (π bs : G) * v⁻¹) * (π bs : G)⁻¹
      have hT : T = (v * (π bs : G) * v⁻¹) * (π bs : G)⁻¹ := rfl
      have hTE : T ∈ E := by
        rw [hT]
        exact E.mul_mem hvpiE (E.inv_mem hpiE)
      have hTN : T ∈ N := hE_le_N hTE
      have hTp : T ^ p = 1 := hE_elem.2 T hTE
      have hTcent : T ∈ Subgroup.centralizer (Bs : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b' hb'
        let bs' : ↥Bs := ⟨b', hb'⟩
        have hbs' : (bs' : G) = b' := rfl
        have hpi'E : (π bs' : G) ∈ E := (hE_mem _).mpr ⟨bs', rfl⟩
        have hTEcomm : T * (π bs' : G) = (π bs' : G) * T :=
          congrArg Subtype.val (hE_elem.1.is_comm.comm ⟨T, hTE⟩ ⟨(π bs' : G), hpi'E⟩)
        have hc'T : ((π bs' : G)⁻¹ * (bs' : G)) * T =
            T * ((π bs' : G)⁻¹ * (bs' : G)) := c_comm bs' ⟨T, hTN⟩
        have hb'dec : b' = (π bs' : G) * ((π bs' : G)⁻¹ * (bs' : G)) := by
          rw [← hbs']
          group
        calc b' * T = ((π bs' : G) * ((π bs' : G)⁻¹ * (bs' : G))) * T := by rw [hb'dec]
          _ = T * ((π bs' : G) * ((π bs' : G)⁻¹ * (bs' : G))) := by
                rw [mul_assoc, hc'T, ← mul_assoc, ← hTEcomm, mul_assoc]
          _ = T * b' := by rw [hb'dec]
      have hTBs : T ∈ Bs := hBs.2.2.2 T hTcent hTp
      have hvcb : v * ((π bs : G)⁻¹ * (bs : G)) * v⁻¹ = (π bs : G)⁻¹ * (bs : G) := by
        have hcomm := c_comm bs ⟨v, hvN⟩
        calc v * ((π bs : G)⁻¹ * (bs : G)) * v⁻¹
            = (((π bs : G)⁻¹ * (bs : G)) * v) * v⁻¹ := by rw [← hcomm]
          _ = (π bs : G)⁻¹ * (bs : G) := by group
      have hbdec : b = (π bs : G) * ((π bs : G)⁻¹ * (bs : G)) := by
        rw [← hbs]
        group
      have hmain : v * b * v⁻¹ = T * b := by
        rw [hbdec, hT]
        calc v * ((π bs : G) * ((π bs : G)⁻¹ * (bs : G))) * v⁻¹
            = (v * (π bs : G) * v⁻¹) * (v * ((π bs : G)⁻¹ * (bs : G)) * v⁻¹) := by group
          _ = (v * (π bs : G) * v⁻¹) * ((π bs : G)⁻¹ * (bs : G)) := by rw [hvcb]
          _ = ((v * (π bs : G) * v⁻¹) * (π bs : G)⁻¹) *
                ((π bs : G) * ((π bs : G)⁻¹ * (bs : G))) := by group
      rw [hmain]
      exact Bs.mul_mem hTBs hb
    have hWnormBs : ∀ w ∈ W, w ∈ Subgroup.normalizer (Bs : Set G) := by
      intro w hwW
      rw [Subgroup.mem_normalizer_iff]
      intro b
      constructor
      · intro hb
        exact key w hwW b hb
      · intro hb
        have h := key w⁻¹ (W.inv_mem hwW) (w * b * w⁻¹) hb
        have h' : w⁻¹ * (w * b * w⁻¹) * (w⁻¹)⁻¹ = b := by group
        rwa [h'] at h
    let f : ↥W → ↥(ggAutomizer N Bs) := fun w =>
      ⟨conjAutOfMem (w : G) (hWnormBs (w : G) w.2),
        Subgroup.subset_closure
          ⟨(w : G), hWN w.2, hWnormBs (w : G) w.2, fun b => conjAutOfMem_apply _ _ b⟩⟩
    have hfinj : Function.Injective f := by
      intro w w' hww'
      have hval : conjAutOfMem (w : G) (hWnormBs (w : G) w.2) =
          conjAutOfMem (w' : G) (hWnormBs (w' : G) w'.2) := congrArg Subtype.val hww'
      have hconj : ∀ b : ↥Bs, (w' : G) * (b : G) * (w' : G)⁻¹ =
          (w : G) * (b : G) * (w : G)⁻¹ := by
        intro b
        have h1 := congrArg (fun ψ : MulAut ↥Bs => ((ψ b : ↥Bs) : G)) hval
        simpa only [conjAutOfMem_apply] using h1.symm
      apply Subtype.ext
      let v : G := (w : G)⁻¹ * (w' : G)
      have hvW : v ∈ W := W.mul_mem (W.inv_mem w.2) w'.2
      have hvN : v ∈ N := hWN hvW
      have hvcent : v ∈ Subgroup.centralizer (E : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        obtain ⟨b, hb⟩ := (hE_mem e).mp he
        have hvb : v * (b : G) * v⁻¹ = (b : G) := by
          dsimp only [v]
          calc ((w : G)⁻¹ * (w' : G)) * (b : G) * ((w : G)⁻¹ * (w' : G))⁻¹
              = (w : G)⁻¹ * ((w' : G) * (b : G) * (w' : G)⁻¹) * (w : G) := by group
            _ = (w : G)⁻¹ * ((w : G) * (b : G) * (w : G)⁻¹) * (w : G) := by rw [hconj b]
            _ = (b : G) := by group
        have hvb_comm : (b : G) * v = v * (b : G) := by
          have h := congrArg (fun x => x * v) hvb
          simpa [mul_assoc] using h.symm
        have hpi_comm : (π b : G) * v = v * (π b : G) := by
          have hdec : (π b : G) = (b : G) * ((π b : G)⁻¹ * (b : G))⁻¹ := by group
          rw [hdec]
          exact mul_inv_comm hvb_comm (c_comm b ⟨v, hvN⟩)
        rw [← hb]
        exact hpi_comm
      have hv1 : v = 1 := hWtriv v hvW hvcent
      dsimp only [v] at hv1
      exact inv_mul_eq_one.mp hv1
    have hcard := Nat.card_le_card_of_injective f hfinj
    simpa using hcard

end CFSG.StandardType

end
