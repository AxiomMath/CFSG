module

public import Certificates.Kernel.BabyMonster.SevenMem

public section

namespace CFSG.KC.BM.SevenElemMem

open CFSG.KC.BM CFSG.KC.BM.MemChain

local notation "sm" => stripMat

variable {S : Submonoid (Matrix (Fin 4370) (Fin 4370) (ZMod 2))}

theorem seven_elem_mem (hA1 : sm Seeds.A1 ∈ S) (hA2 : sm Seeds.A2 ∈ S) :
    sm Seven.g ∈ S ∧ sm Seven.al ∈ S ∧ sm Seven.t1 ∈ S ∧ sm Seven.e3 ∈ S := by
  obtain ⟨m_g, -, -, -, m_al, m_t1⟩ := SevenMem.seven_mem_all hA1 hA2
  have m_r32 : sm Seven.r32 ∈ S := SevenMem.memN Seven.wf_g m_g
    (SevenMem.fc Seven.wf_g m_g <| SevenMem.fn) (by bm_strips CFSG.KC.BM.Seven.c_r32 69)
  have m_r33 : sm Seven.r33 ∈ S := SevenMem.memN Seven.wf_r32 m_r32
    (SevenMem.fc Seven.wf_r32 m_r32 <| SevenMem.fn) (by bm_strips CFSG.KC.BM.Seven.c_r33 69)
  have m_r34 : sm Seven.r34 ∈ S := SevenMem.memN Seven.wf_r33 m_r33
    (SevenMem.fc Seven.wf_r33 m_r33 <| SevenMem.fn) (by bm_strips CFSG.KC.BM.Seven.c_r34 69)
  have m_x : sm Seven.x ∈ S := SevenMem.memN Seven.wf_r32 m_r32
    (SevenMem.fc Seven.wf_r34 m_r34 <| SevenMem.fn) (by bm_strips CFSG.KC.BM.Seven.c_x 69)
  have m_y : sm Seven.y ∈ S := SevenMem.memN Seven.wf_r33 m_r33
    (SevenMem.fc Seven.wf_x m_x <| SevenMem.fn) (by bm_strips CFSG.KC.BM.Seven.c_y 69)
  have m_y2 : sm Seven.y2 ∈ S := SevenMem.memN Seven.wf_y m_y
    (SevenMem.fc Seven.wf_y m_y <| SevenMem.fn) (by bm_strips CFSG.KC.BM.Seven.c_y2 69)
  have m_y4 : sm Seven.y4 ∈ S := SevenMem.memN Seven.wf_y2 m_y2
    (SevenMem.fc Seven.wf_y2 m_y2 <| SevenMem.fn) (by bm_strips CFSG.KC.BM.Seven.c_y4 69)
  have m_r43 : sm Seven.r43 ∈ S := SevenMem.memN Seven.wf_t1 m_t1
    (SevenMem.fc Seven.wf_y m_y <| SevenMem.fn) (by bm_strips CFSG.KC.BM.Seven.c_r43 69)
  have m_r40 : sm Seven.r40 ∈ S := SevenMem.memN Seven.wf_t1 m_t1
    (SevenMem.fc Seven.wf_y4 m_y4 <| SevenMem.fn) (by bm_strips CFSG.KC.BM.Seven.c_r40 69)
  have m_r44 : sm Seven.r44 ∈ S := SevenMem.memN Seven.wf_r40 m_r40
    (SevenMem.fc Seven.wf_r40 m_r40 <| SevenMem.fn) (by bm_strips CFSG.KC.BM.Seven.c_r44 69)
  have m_r47 : sm Seven.r47 ∈ S := SevenMem.memN Seven.wf_r43 m_r43
    (SevenMem.fc Seven.wf_r44 m_r44 <| SevenMem.fn) (by bm_strips CFSG.KC.BM.Seven.c_r47 69)
  have m_e3 : sm Seven.e3 ∈ S := SevenMem.memN Seven.wf_r43 m_r43
    (SevenMem.fc Seven.wf_r47 m_r47 <| SevenMem.fc Seven.wf_r43 m_r43 <|
      SevenMem.fc Seven.wf_y m_y <| SevenMem.fc Seven.wf_r47 m_r47 <|
      SevenMem.fc Seven.wf_r44 m_r44 <| SevenMem.fc Seven.wf_r44 m_r44 <|
      SevenMem.fc Seven.wf_r40 m_r40 <| SevenMem.fc Seven.wf_r43 m_r43 <|
      SevenMem.fc Seven.wf_r40 m_r40 <| SevenMem.fc Seven.wf_y4 m_y4 <|
      SevenMem.fc Seven.wf_r43 m_r43 <| SevenMem.fn)
    (by bm_strips CFSG.KC.BM.Seven.c_e3 69)
  exact ⟨m_g, m_al, m_t1, m_e3⟩

end CFSG.KC.BM.SevenElemMem

end
